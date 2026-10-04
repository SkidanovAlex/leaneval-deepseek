import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Localisation on the flat torus

The STE development (`Submission/Work/Diff/STE/DESIGN.md`) solves the DeTurck equation
locally in charts and glues the local solutions.  The gluing needs, on the flat torus
`𝕋ⁿ = ℝⁿ / ℤⁿ`, a *finite* smooth partition of unity whose pieces are supported in small cubes,
together with the *coordinate* maps that translate each cube back to the origin.

This file provides that data.  Concretely it produces

* finitely many "centres" `c j ∈ [0,1)ⁿ` (here `j : Fin n → Fin 4`, `c j p = (j p)/4`),
* smooth `1`-periodic maps `φ j : ℝⁿ → ℝⁿ` with the property that on the support of `η j` the map
  `φ j` is a lattice translation of `x ↦ x - c j`:
  `η j x ≠ 0 → ∃ m : Fin n → ℤ, ∀ p, φ j x p = x p - c j p + m p`,
* a smooth `1`-periodic partition of unity `η : ι → ℝⁿ → ℝ`, `η j ≥ 0`, `∑ j, η j = 1`, with
  `support (η j)` contained in the region where `φ j` is such a translation,
* uniform bounds on the weighted `ℓ²` norms of the Fourier coefficients of the pieces
  (`Work.Diff.STE.CSq ρ`).

## Construction

* `bumpB n` is a bump on `ℝⁿ` (sup-norm cube of radius `1/8`, support in the ball of radius
  `3/8`), `bumpH` is a bump on `ℝ` (`1` on `[-3/8,3/8]`, support in `(-49/100,49/100)`).
* `B` is the periodisation `∑_{m ∈ ℤⁿ} b (y + m)` of the first bump.  It is `1` on a neighbourhood
  of every lattice point and vanishes outside the union of the balls of radius `3/8`, so it is a
  "smooth indicator of `ℤⁿ`".
* `R p` is the periodisation of `z ↦ z p · ∏ q, h (z q)`; near a lattice point `m` it equals the
  coordinate `y p + m p`, i.e. it is a periodised "rounding" map.
* `φ j = R (x - c j)` and `η j = (B (x - c j))² / ∑ j', (B (x - c j'))²`.  The denominator is
  `≥ 1` because the cubes `c j + [-1/8,1/8]ⁿ` cover `ℝⁿ`; hence the `η j` form a partition of
  unity, and on the support of `η j` the point `x - c j` is within `3/8` of a lattice vector, so
  `R` is exactly the corresponding rounding.
-/

noncomputable section

namespace Work.Diff.STE.flat

open BigOperators Function

/-! ## Auxiliary: smoothness of finite products -/

lemma contDiff_finset_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) (n : ℕ∞) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using contDiff_const (c := (1 : ℝ))
  | insert a s ha ih =>
      have hstep : (fun x : E => ∏ i ∈ insert a s, f i x)
          = (fun x : E => f a x * ∏ i ∈ s, f i x) := by
        funext x
        rw [Finset.prod_insert ha]
      rw [hstep]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-! ## The bumps -/

/-- The bump `b` on `ℝⁿ`: `1` on the closed cube of radius `1/8` (in the sup norm) and supported
in the open ball of radius `3/8`. -/
def bumpB (n : ℕ) : ContDiffBump (0 : Fin n → ℝ) := ⟨1/8, 3/8, by norm_num, by norm_num⟩

/-- The bump `h` on `ℝ`: `1` on `[-3/8, 3/8]` and supported in the ball of radius `49/100`. -/
def bumpH : ContDiffBump (0 : ℝ) := ⟨3/8, 49/100, by norm_num, by norm_num⟩

/-- `b` as a function. -/
def bB (n : ℕ) : (Fin n → ℝ) → ℝ := fun z => bumpB n z

/-- `h` as a function. -/
def hH : ℝ → ℝ := fun t => bumpH t

@[simp] lemma bB_apply (n : ℕ) (z : Fin n → ℝ) : bB n z = bumpB n z := rfl

@[simp] lemma hH_apply (t : ℝ) : hH t = bumpH t := rfl

lemma bB_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bB n) := ContDiffBump.contDiff (bumpB n)

lemma hH_contDiff : ContDiff ℝ (⊤ : ℕ∞) hH := ContDiffBump.contDiff bumpH

lemma bB_one (n : ℕ) {z : Fin n → ℝ} (hz : ‖z‖ ≤ 1/8) : bB n z = 1 := by
  rw [bB_apply]
  apply ContDiffBump.one_of_mem_closedBall
  rw [show (bumpB n).rIn = 1/8 from rfl, Metric.mem_closedBall, dist_zero_right]
  exact hz

lemma hH_one {t : ℝ} (ht : |t| ≤ 3/8) : hH t = 1 := by
  rw [hH_apply]
  apply ContDiffBump.one_of_mem_closedBall
  rw [show (bumpH).rIn = 3/8 from rfl, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact ht

lemma bB_eq_zero (n : ℕ) {z : Fin n → ℝ} (hz : 3/8 ≤ ‖z‖) : bB n z = 0 := by
  by_contra hc
  have hmem : z ∈ Function.support (bumpB n) := by
    rw [Function.mem_support]; rwa [bB_apply] at hc
  rw [ContDiffBump.support_eq] at hmem
  simp only [Metric.mem_ball, dist_zero_right] at hmem
  rw [show (bumpB n).rOut = 3/8 from rfl] at hmem
  linarith

lemma hH_eq_zero {t : ℝ} (ht : 49/100 ≤ |t|) : hH t = 0 := by
  by_contra hc
  have hmem : t ∈ Function.support (bumpH) := by
    rw [Function.mem_support]; rwa [hH_apply] at hc
  rw [ContDiffBump.support_eq] at hmem
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  rw [show (bumpH).rOut = 49/100 from rfl] at hmem
  linarith

lemma bB_support_subset (n : ℕ) :
    Function.support (bB n) ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2 : ℝ)) (1/2)) := by
  intro z hz
  rw [Set.mem_pi]
  intro p _
  have hmem : z ∈ Function.support (bumpB n) := by
    rw [Function.mem_support]
    rwa [Function.mem_support, bB_apply] at hz
  rw [ContDiffBump.support_eq] at hmem
  simp only [Metric.mem_ball, dist_zero_right] at hmem
  rw [show (bumpB n).rOut = 3/8 from rfl] at hmem
  have h1 : |z p| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm z p
  have h2 : -‖z‖ ≤ z p := (abs_le.mp h1).1
  have h3 : z p ≤ ‖z‖ := (abs_le.mp h1).2
  rw [Set.mem_Ioo]
  constructor <;> linarith

/-! ## Periodisation of a real-valued function -/

/-- The periodisation of a smooth real-valued function supported in the open unit cube, taken
through `ℂ` and projected back to `ℝ`, is smooth and `1`-periodic. -/
lemma periodization_re_contDiff_periodic {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2 : ℝ)) (1/2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ =>
        (∑' m : Fin n → ℤ, ((f (y + iVec m) : ℝ) : ℂ)).re) ∧
      Periodic1 (fun y : Fin n → ℝ =>
        (∑' m : Fin n → ℤ, ((f (y + iVec m) : ℝ) : ℂ)).re) := by
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => Complex.ofRealCLM (f z)) :=
      Complex.ofRealCLM.contDiff.comp hf
    simpa only [Complex.ofRealCLM_apply] using h
  have hsuppC : Function.support (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2 : ℝ)) (1/2)) := by
    intro z hz
    rw [Function.mem_support] at hz
    apply hsupp
    rw [Function.mem_support]
    intro h0
    exact hz (by rw [h0, Complex.ofReal_zero])
  obtain ⟨h1, h2, -⟩ := periodization_contDiff_periodic (ι := Fin n)
    (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) hfC hsuppC
  refine ⟨?_, ?_⟩
  · have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ =>
        Complex.reCLM (∑' m : Fin n → ℤ, ((f (y + iVec m) : ℝ) : ℂ))) :=
      Complex.reCLM.contDiff.comp h1
    simpa only [Complex.reCLM_apply] using h
  · intro i y
    exact congrArg Complex.re (h2 i y)

/-! ## The periodised bump `B` and the periodised rounding `R` -/

/-- The periodisation of the bump `b`, as a complex-valued function. -/
def Bc (n : ℕ) (y : Fin n → ℝ) : ℂ :=
  ∑' m : Fin n → ℤ, ((bB n (y + iVec m) : ℝ) : ℂ)

/-- The periodised bump `B y = ∑_{m ∈ ℤⁿ} b (y + m)`. -/
def B (n : ℕ) (y : Fin n → ℝ) : ℝ := (Bc n y).re

lemma B_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (B n) :=
  (periodization_re_contDiff_periodic (bB n) (bB_contDiff n) (bB_support_subset n)).1

lemma B_periodic (n : ℕ) : Periodic1 (B n) :=
  (periodization_re_contDiff_periodic (bB n) (bB_contDiff n) (bB_support_subset n)).2

/-- The function `z ↦ z p · ∏ q, h (z q)` whose periodisation is the `p`-th component of the
rounding map. -/
def gH (n : ℕ) (p : Fin n) : (Fin n → ℝ) → ℝ := fun z => z p * ∏ q, hH (z q)

lemma gH_contDiff (n : ℕ) (p : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (gH n p) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => z p * ∏ q, hH (z q)) := by
    refine ContDiff.mul (contDiff_apply ℝ ℝ p) ?_
    exact contDiff_finset_prod Finset.univ ⊤ (fun q => fun z : Fin n → ℝ => hH (z q))
      (fun q _ => hH_contDiff.comp (contDiff_apply ℝ ℝ q))
  exact h

lemma gH_support_subset (n : ℕ) (p : Fin n) :
    Function.support (gH n p) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2 : ℝ)) (1/2)) := by
  intro z hz
  rw [Set.mem_pi]
  intro q _
  rw [Set.mem_Ioo]
  have hz0 : gH n p z ≠ 0 := hz
  have hprod : ∏ q, hH (z q) ≠ 0 := by
    intro h0
    refine hz0 ?_
    have : gH n p z = z p * ∏ q, hH (z q) := rfl
    rw [this, h0, mul_zero]
  have hq : hH (z q) ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) q (Finset.mem_univ q)
  have hmem : z q ∈ Function.support (bumpH) := by
    rw [Function.mem_support]; rwa [hH_apply] at hq
  rw [ContDiffBump.support_eq] at hmem
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  rw [show (bumpH).rOut = 49/100 from rfl] at hmem
  have h2 : -(1/2 : ℝ) < z q := by linarith [(abs_lt.mp hmem).1]
  have h3 : z q < 1/2 := by linarith [(abs_lt.mp hmem).2]
  constructor <;> linarith

/-- The periodisation of `gH n p`, as a complex-valued function. -/
def Rc (n : ℕ) (p : Fin n) (y : Fin n → ℝ) : ℂ :=
  ∑' m : Fin n → ℤ, ((gH n p (y + iVec m) : ℝ) : ℂ)

/-- The `p`-th component of the periodised rounding map. -/
def R (n : ℕ) (p : Fin n) (y : Fin n → ℝ) : ℝ := (Rc n p y).re

lemma R_contDiff (n : ℕ) (p : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (R n p) :=
  (periodization_re_contDiff_periodic (gH n p) (gH_contDiff n p) (gH_support_subset n p)).1

lemma R_periodic (n : ℕ) (p : Fin n) : Periodic1 (R n p) :=
  (periodization_re_contDiff_periodic (gH n p) (gH_contDiff n p) (gH_support_subset n p)).2

/-! ## The rounding lemmas -/

/-- If `v` is a nonzero integer vector, its sup norm (as a real vector) is at least `1`. -/
lemma one_le_norm_iVec {n : ℕ} {v : Fin n → ℤ} (hv : v ≠ 0) : (1 : ℝ) ≤ ‖iVec v‖ := by
  obtain ⟨q, hq⟩ : ∃ q, v q ≠ 0 := by
    by_contra h
    exact hv (funext (by simpa using not_exists.mp h))
  have h1 : (1 : ℤ) ≤ |v q| := Int.one_le_abs hq
  have h2 : (1 : ℝ) ≤ |((v q : ℤ) : ℝ)| := by exact_mod_cast h1
  have h3 : |((v q : ℤ) : ℝ)| ≤ ‖iVec v‖ := by
    have := norm_le_pi_norm (iVec v) q
    simpa only [iVec_apply, Real.norm_eq_abs] using this
  linarith

/-- The periodised bump equals `1` near the lattice points. -/
lemma B_eq_one (n : ℕ) {y : Fin n → ℝ} {m : Fin n → ℤ} (hm : ‖y + iVec m‖ ≤ 1/8) :
    B n y = 1 := by
  have hsum : Bc n y = 1 := by
    rw [Bc]
    have h : (∑' m' : Fin n → ℤ, ((bB n (y + iVec m') : ℝ) : ℂ))
        = ((bB n (y + iVec m) : ℝ) : ℂ) :=
      tsum_eq_single
      (f := fun m' : Fin n → ℤ => ((bB n (y + iVec m') : ℝ) : ℂ)) m (fun m' hm' => by
        have h0 : bB n (y + iVec m') = 0 := by
          apply bB_eq_zero
          have h1 : (1 : ℝ) ≤ ‖iVec (m' - m)‖ :=
            one_le_norm_iVec (sub_ne_zero.mpr hm')
          have h2 : ‖iVec (m' - m)‖ ≤ ‖y + iVec m'‖ + ‖y + iVec m‖ := by
            have hdecomp : y + iVec m' - (y + iVec m) = iVec (m' - m) := by
              funext q
              simp only [Pi.sub_apply, Pi.add_apply, iVec_apply]
              push_cast
              ring
            calc ‖iVec (m' - m)‖ = ‖(y + iVec m') - (y + iVec m)‖ := by rw [hdecomp]
              _ ≤ ‖y + iVec m'‖ + ‖y + iVec m‖ := norm_sub_le _ _
          linarith
        rw [h0, Complex.ofReal_zero])
    rw [h, bB_one n hm, Complex.ofReal_one]
  rw [B, hsum]
  simp

/-- If the periodised bump does not vanish at `y`, then `y` is within `3/8` of a lattice point. -/
lemma B_exists_lattice (n : ℕ) {y : Fin n → ℝ} (h : B n y ≠ 0) :
    ∃ m : Fin n → ℤ, ‖y + iVec m‖ < 3/8 := by
  have hc : Bc n y ≠ 0 := by
    intro h0
    exact h (by rw [B, h0]; simp)
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hzero : Bc n y = 0 := by
    rw [Bc]
    have h : (∑' m : Fin n → ℤ, ((bB n (y + iVec m) : ℝ) : ℂ))
        = ∑' _ : Fin n → ℤ, (0 : ℂ) :=
      tsum_congr (fun m => by rw [bB_eq_zero n (hcon m), Complex.ofReal_zero])
    rw [h, tsum_zero]
  exact hc hzero

/-- The periodised rounding is exact near the lattice points. -/
lemma R_eq (n : ℕ) (p : Fin n) {y : Fin n → ℝ} {m : Fin n → ℤ}
    (hm : ‖y + iVec m‖ ≤ 3/8) : R n p y = y p + (m p : ℝ) := by
  have hprod1 : ∏ q, hH ((y + iVec m) q) = 1 := by
    apply Finset.prod_eq_one
    intro q _
    apply hH_one
    have h1 : |((y + iVec m) q)| ≤ ‖y + iVec m‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (y + iVec m) q
    linarith
  have hg : gH n p (y + iVec m) = y p + (m p : ℝ) := by
    have h0 : gH n p (y + iVec m)
        = (y + iVec m) p * ∏ q, hH ((y + iVec m) q) := rfl
    rw [h0, hprod1, mul_one]
    simp only [Pi.add_apply, iVec_apply]
  have hsum : Rc n p y = ((y p + (m p : ℝ) : ℝ) : ℂ) := by
    rw [Rc]
    have h : (∑' m' : Fin n → ℤ, ((gH n p (y + iVec m') : ℝ) : ℂ))
        = ((gH n p (y + iVec m) : ℝ) : ℂ) :=
      tsum_eq_single
      (f := fun m' : Fin n → ℤ => ((gH n p (y + iVec m') : ℝ) : ℂ)) m (fun m' hm' => by
        have h0 : gH n p (y + iVec m') = 0 := by
          obtain ⟨q, hq⟩ : ∃ q, m' q ≠ m q := by
            by_contra h
            exact hm' (funext (by simpa using not_exists.mp h))
          have hq' : (m' - m) q ≠ 0 := by
            show m' q - m q ≠ 0
            exact sub_ne_zero.mpr hq
          have hfac : hH ((y + iVec m') q) = 0 := by
            apply hH_eq_zero
            have h1 : (1 : ℝ) ≤ |(((m' - m) q : ℤ) : ℝ)| := by
              have := Int.one_le_abs hq'
              exact_mod_cast this
            have hdecomp : (y + iVec m') q = (y + iVec m) q + (((m' - m) q : ℤ) : ℝ) := by
              simp only [Pi.add_apply, iVec_apply, Pi.sub_apply]
              push_cast
              ring
            have h2 : |(((m' - m) q : ℤ) : ℝ)| ≤ |(y + iVec m) q| + |(y + iVec m') q| := by
              have hb : (((m' - m) q : ℤ) : ℝ) = (y + iVec m') q - (y + iVec m) q := by
                linarith [hdecomp]
              rw [hb]
              refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
              · linarith [le_abs_self ((y + iVec m') q), neg_le_abs ((y + iVec m) q)]
              · linarith [le_abs_self ((y + iVec m) q), neg_le_abs ((y + iVec m') q)]
            have h3 : |(y + iVec m) q| ≤ ‖y + iVec m‖ := by
              simpa only [Real.norm_eq_abs] using norm_le_pi_norm (y + iVec m) q
            linarith
          have hgg : gH n p (y + iVec m')
              = (y + iVec m') p * ∏ q, hH ((y + iVec m') q) := rfl
          rw [hgg, Finset.prod_eq_zero (Finset.mem_univ q) hfac, mul_zero]
        rw [h0, Complex.ofReal_zero])
    rw [h, hg]
  rw [R, hsum, Complex.ofReal_re]

/-! ## The covering lemma for the grid `c j p = (j p)/4` -/

/-- The grid `(j/4)_{j ∈ {0,1,2,3}} + ℤ` covers `ℝ` with cubes of radius `1/8`. -/
lemma grid_cover_one (x : ℝ) :
    ∃ (j : Fin 4) (m : ℤ), |x - (j : ℝ)/4 - (m : ℝ)| ≤ 1/8 := by
  set k : ℤ := ⌊4 * x + 1/2⌋ with hkdef
  have hk1 : (k : ℝ) ≤ 4 * x + 1/2 := Int.floor_le _
  have hk2 : 4 * x + 1/2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hmod0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
  have hmod4 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨⟨(k % 4).toNat, by omega⟩, k / 4, ?_⟩
  have hcase_int : ((k % 4).toNat : ℤ) = k - 4 * (k / 4) := by
    rw [Int.toNat_of_nonneg hmod0]
    have h := Int.mul_ediv_add_emod k 4
    linarith
  have hcase : ((k % 4).toNat : ℝ) = (k : ℝ) - 4 * ((k / 4 : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcase_int
    push_cast at this
    linarith
  have hgoal : x - ((⟨(k % 4).toNat, by omega⟩ : Fin 4) : ℝ)/4 - ((k / 4 : ℤ) : ℝ)
      = x - (k : ℝ)/4 := by
    simp only [Fin.val_mk]
    rw [hcase]
    ring
  rw [hgoal, abs_le]
  constructor <;> linarith

/-- **Grid covering lemma.**  For every `x : ℝⁿ` there are `j : Fin n → Fin 4` and
`m : Fin n → ℤ` with `|x p - (j p)/4 - m p| ≤ 1/8` for all `p`. -/
theorem grid_cover (n : ℕ) (x : Fin n → ℝ) :
    ∃ (j : Fin n → Fin 4) (m : Fin n → ℤ),
      ∀ p : Fin n, |x p - (j p : ℝ) / 4 - (m p : ℝ)| ≤ 1 / 8 := by
  have h : ∀ p : Fin n, ∃ (j : Fin 4) (m : ℤ),
      |x p - (j : ℝ)/4 - (m : ℝ)| ≤ 1/8 := fun p => grid_cover_one (x p)
  choose j m hm using h
  exact ⟨j, m, hm⟩

/-! ## The localisation data -/

/-- The centres `c j p = (j p)/4 ∈ {0, 1/4, 1/2, 3/4}`. -/
def cShot (n : ℕ) (j : Fin n → Fin 4) : Fin n → ℝ := fun p => (j p : ℝ)/4

/-- The localisation map of the chart `j`. -/
def phiF (n : ℕ) (j : Fin n → Fin 4) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun p => R n p (x - cShot n j)

/-- The partition of unity. -/
def etaF (n : ℕ) (j : Fin n → Fin 4) (x : Fin n → ℝ) : ℝ :=
  (B n (x - cShot n j))^2 / (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2)

lemma cShot_bounds (n : ℕ) (j : Fin n → Fin 4) (p : Fin n) :
    0 ≤ cShot n j p ∧ cShot n j p < 1 := by
  have hj : (j p : ℝ) < 4 := by
    have h : ((j p : ℕ) : ℝ) < 4 := by
      have := (j p).isLt
      exact_mod_cast this
    exact h
  have h0 : (0 : ℝ) ≤ (j p : ℝ) := Nat.cast_nonneg _
  have hc : cShot n j p = (j p : ℝ)/4 := rfl
  rw [hc]
  constructor <;> linarith

lemma phiF_contDiff (n : ℕ) (j : Fin n → Fin 4) : ContDiff ℝ (⊤ : ℕ∞) (phiF n j) := by
  rw [contDiff_pi]
  intro p
  exact (R_contDiff n p).comp (contDiff_id.sub contDiff_const)

lemma phiF_periodic (n : ℕ) (j : Fin n → Fin 4) : Periodic1 (phiF n j) := by
  intro i x
  funext p
  show R n p ((x + Pi.single i 1) - cShot n j) = R n p (x - cShot n j)
  rw [show (x + Pi.single i 1) - cShot n j = (x - cShot n j) + Pi.single i 1 from by abel]
  exact R_periodic n p i (x - cShot n j)

/-- The denominator of the partition of unity is at least `1` everywhere. -/
lemma one_le_denom (n : ℕ) (x : Fin n → ℝ) :
    (1 : ℝ) ≤ ∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2 := by
  obtain ⟨j₀, m, hm⟩ := grid_cover n x
  have hB : B n (x - cShot n j₀) = 1 := by
    apply B_eq_one
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/8)]
    intro p
    have h1 : ((x - cShot n j₀) + iVec (-m)) p = x p - (j₀ p : ℝ)/4 - (m p : ℝ) := by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, iVec_apply, cShot]
      push_cast
      ring
    rw [h1]
    exact hm p
  calc (1 : ℝ) = (B n (x - cShot n j₀))^2 := by rw [hB]; norm_num
    _ ≤ ∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2 :=
        Finset.single_le_sum (f := fun j' => (B n (x - cShot n j'))^2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j₀)

lemma etaF_contDiff (n : ℕ) (j : Fin n → Fin 4) : ContDiff ℝ (⊤ : ℕ∞) (etaF n j) := by
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (B n (x - cShot n j))^2) :=
    ((B_contDiff n).comp (contDiff_id.sub contDiff_const)).pow 2
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => ∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) :=
    ContDiff.sum (fun j' _ =>
      ((B_contDiff n).comp (contDiff_id.sub contDiff_const)).pow 2)
  have hdiv := hnum.div hden (fun x =>
    ne_of_gt (lt_of_lt_of_le one_pos (one_le_denom n x)))
  exact hdiv

lemma etaF_periodic (n : ℕ) (j : Fin n → Fin 4) : Periodic1 (etaF n j) := by
  intro i x
  have h1 : B n ((x + Pi.single i 1) - cShot n j) = B n (x - cShot n j) := by
    rw [show (x + Pi.single i 1) - cShot n j = (x - cShot n j) + Pi.single i 1 from by abel]
    exact B_periodic n i (x - cShot n j)
  have h2 : (∑ j' : Fin n → Fin 4, (B n ((x + Pi.single i 1) - cShot n j'))^2) =
      (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) := by
    apply Finset.sum_congr rfl
    intro j' _
    rw [show (x + Pi.single i 1) - cShot n j' = (x - cShot n j') + Pi.single i 1 from by abel]
    rw [B_periodic n i (x - cShot n j')]
  have heta : etaF n j (x + Pi.single i 1)
      = (B n ((x + Pi.single i 1) - cShot n j))^2
        / (∑ j' : Fin n → Fin 4, (B n ((x + Pi.single i 1) - cShot n j'))^2) := rfl
  rw [heta, h1, h2]
  rfl

lemma etaF_nonneg (n : ℕ) (j : Fin n → Fin 4) (x : Fin n → ℝ) : 0 ≤ etaF n j x := by
  have h0 : etaF n j x = (B n (x - cShot n j))^2
      / (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) := rfl
  rw [h0]
  exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

lemma sum_etaF (n : ℕ) (x : Fin n → ℝ) : ∑ j : Fin n → Fin 4, etaF n j x = 1 := by
  have hpos : (0 : ℝ) < ∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2 :=
    lt_of_lt_of_le one_pos (one_le_denom n x)
  have hfun : ∀ j : Fin n → Fin 4, etaF n j x = (B n (x - cShot n j))^2
      / (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) := fun j => rfl
  calc ∑ j : Fin n → Fin 4, etaF n j x
      = ∑ j : Fin n → Fin 4, (B n (x - cShot n j))^2
          / (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) := by
        exact Finset.sum_congr rfl (fun j _ => hfun j)
    _ = (∑ j : Fin n → Fin 4, (B n (x - cShot n j))^2)
          / (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) := by
        rw [Finset.sum_div]
    _ = 1 := div_self (ne_of_gt hpos)

/-- On the support of `η j`, the map `φ j` translates the point back to the cube of the chart. -/
lemma etaF_localization (n : ℕ) {j : Fin n → Fin 4} {x : Fin n → ℝ} (h : etaF n j x ≠ 0) :
    ∃ m : Fin n → ℤ, ∀ p, phiF n j x p = x p - cShot n j p + (m p : ℝ) := by
  have hB : B n (x - cShot n j) ≠ 0 := by
    intro h0
    refine h ?_
    have : etaF n j x = (B n (x - cShot n j))^2
        / (∑ j' : Fin n → Fin 4, (B n (x - cShot n j'))^2) := rfl
    rw [this, h0]
    simp
  obtain ⟨m, hm⟩ := B_exists_lattice n hB
  refine ⟨m, fun p => ?_⟩
  have hphi : phiF n j x p = R n p (x - cShot n j) := rfl
  rw [hphi, R_eq n p (le_of_lt hm)]
  simp only [Pi.sub_apply]

/-! ## Uniform Fourier bounds (finiteness of the family of pieces) -/

lemma exists_CSq_bound_phi (n ρ : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin n → Fin 4) (p : Fin n),
      CSq ρ (fourierCoeff (fun x : Fin n → ℝ => ((phiF n j x p : ℝ) : ℂ))) ≤ C := by
  classical
  refine ⟨max 1 ((Finset.univ : Finset ((Fin n → Fin 4) × Fin n)).sup'
      ⟨(fun _ : Fin n => (0 : Fin 4), ⟨0, by omega⟩), Finset.mem_univ _⟩
      (fun jp => CSq ρ (fourierCoeff (fun x : Fin n → ℝ => ((phiF n jp.1 x jp.2 : ℝ) : ℂ))))),
    le_trans zero_le_one (le_max_left (1 : ℝ) _), ?_⟩
  intro j p
  exact le_trans (Finset.le_sup'
      (fun jp : (Fin n → Fin 4) × Fin n =>
        CSq ρ (fourierCoeff (fun x : Fin n → ℝ => ((phiF n jp.1 x jp.2 : ℝ) : ℂ))))
      (Finset.mem_univ (j, p))) (le_max_right _ _)

lemma exists_CSq_bound_eta (n ρ : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : Fin n → Fin 4,
      CSq ρ (fourierCoeff (fun x : Fin n → ℝ => ((etaF n j x : ℝ) : ℂ))) ≤ C := by
  classical
  refine ⟨max 1 ((Finset.univ : Finset (Fin n → Fin 4)).sup'
      ⟨(fun _ : Fin n => (0 : Fin 4)), Finset.mem_univ _⟩
      (fun j => CSq ρ (fourierCoeff (fun x : Fin n → ℝ => ((etaF n j x : ℝ) : ℂ))))),
    le_trans zero_le_one (le_max_left (1 : ℝ) _), ?_⟩
  intro j
  exact le_trans (Finset.le_sup'
      (fun j : Fin n → Fin 4 =>
        CSq ρ (fourierCoeff (fun x : Fin n → ℝ => ((etaF n j x : ℝ) : ℂ))))
      (Finset.mem_univ j)) (le_max_right _ _)

/-! ## The target -/

theorem torus_localization (n : ℕ) (hn : 1 ≤ n) (ρ : ℕ) (hρ : 1 ≤ ρ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (c : ι → (Fin n → ℝ))
      (φ : ι → (Fin n → ℝ) → (Fin n → ℝ)) (η : ι → (Fin n → ℝ) → ℝ),
      (∀ j p, 0 ≤ c j p ∧ c j p < 1) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) ∧
      (∀ j, Work.Diff.STE.Periodic1 (φ j)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (η j)) ∧
      (∀ j, Work.Diff.STE.Periodic1 (η j)) ∧
      (∀ j x, 0 ≤ η j x) ∧
      (∀ x, ∑ j, η j x = 1) ∧
      (∀ j x, η j x ≠ 0 → ∃ m : Fin n → ℤ, ∀ p, φ j x p = x p - c j p + (m p : ℝ)) ∧
      (∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ j p,
        Work.Diff.STE.CSq ρ (Work.Diff.STE.fourierCoeff (fun x => ((φ j x p : ℝ) : ℂ))) ≤ Cφ) ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ j,
        Work.Diff.STE.CSq ρ (Work.Diff.STE.fourierCoeff (fun x => ((η j x : ℝ) : ℂ))) ≤ Cη) := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_CSq_bound_phi n ρ hn
  obtain ⟨Cη, hCη0, hCη⟩ := exists_CSq_bound_eta n ρ hn
  refine ⟨Fin n → Fin 4, inferInstance, inferInstance, cShot n, phiF n, etaF n,
    fun j p => cShot_bounds n j p,
    fun j => phiF_contDiff n j,
    fun j => phiF_periodic n j,
    fun j => etaF_contDiff n j,
    fun j => etaF_periodic n j,
    fun j x => etaF_nonneg n j x,
    fun x => sum_etaF n x,
    fun j x h => etaF_localization n h,
    ⟨Cφ, hCφ0, fun j p => hCφ j p⟩,
    ⟨Cη, hCη0, fun j => hCη j⟩⟩

end Work.Diff.STE.flat
