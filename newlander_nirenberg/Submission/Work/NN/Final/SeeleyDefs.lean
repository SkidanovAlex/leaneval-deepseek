/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Seeley extension operator: definitions

Given weights `a : ℕ → ℝ` and scales `b : ℕ → ℝ` with the moment identities
`∑' m, a m * (-(b m))^j = 1` we construct the (linear) Seeley extension operator
for functions on the half space `{p : X × ℝ | 0 < p.2}`.

This file contains the definitions and the elementary properties (linearity, agreement on the
half space, local finiteness of the sum on the negative half space).
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The cutoff -/

/-- The smooth cutoff of the Seeley extension: `1` on `[-1,1]`, `0` outside `[-2,2]`. -/
def seeleyCut : ℝ → ℝ := (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ))

lemma seeleyCut_contDiff : ContDiff ℝ ∞ seeleyCut := ContDiffBump.contDiff _

lemma seeleyCut_eq_one {t : ℝ} (ht : |t| ≤ 1) : seeleyCut t = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by rw [Metric.mem_closedBall, Real.dist_eq]; simpa using ht)

lemma seeleyCut_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : seeleyCut t = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]; simpa using ht

lemma seeleyCut_nonneg (t : ℝ) : 0 ≤ seeleyCut t :=
  ContDiffBump.nonneg (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) (x := t)

lemma seeleyCut_le_one (t : ℝ) : seeleyCut t ≤ 1 :=
  ContDiffBump.le_one (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) (x := t)

lemma seeleyCut_eventually_eq_one : seeleyCut =ᶠ[𝓝 (0 : ℝ)] (fun _ => 1) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
  exact ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall ht)

lemma seeleyCut_eq_one_of_abs_lt_one {t : ℝ} (ht : |t| < 1) : seeleyCut t = 1 :=
  seeleyCut_eq_one (le_of_lt ht)

/-- the cutoff is locally constant `1` at `0`. -/
lemma seeleyCut_eventually_eq_one' : seeleyCut =ᶠ[𝓝 (0 : ℝ)] (fun _ => 1) :=
  seeleyCut_eventually_eq_one

/-- Uniform bound on the `j`-th iterated derivative of the cutoff. -/
lemma exists_seeleyCut_iteratedFDeriv_bound (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ j seeleyCut t‖ ≤ B := by
  have hcont : Continuous (fun t : ℝ => iteratedFDeriv ℝ j seeleyCut t) :=
    seeleyCut_contDiff.continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hcont.continuousOn (s := Set.Icc (-2 : ℝ) 2))
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : |t| ≤ 2
  · refine le_trans (hC t ?_) (le_max_left _ _)
    exact Set.mem_Icc.mpr (abs_le.mp ht)
  · push_neg at ht
    have hneigh : ∀ᶠ s in 𝓝 t, seeleyCut s = 0 := by
      filter_upwards [Metric.ball_mem_nhds t (show (0:ℝ) < (|t| - 2)/2 by linarith)] with s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      refine seeleyCut_eq_zero (le_of_lt ?_)
      have h2 : |t| - |s - t| ≤ |s| := by
        have h := abs_sub_abs_le_abs_sub t s
        rw [abs_sub_comm] at h
        linarith
      have h3 : (|t| + 2)/2 < |s| := by linarith
      linarith
    have hev : seeleyCut =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := hneigh
    have h0 : iteratedFDeriv ℝ j seeleyCut t = iteratedFDeriv ℝ j (fun _ : ℝ => (0:ℝ)) t :=
      (hev.iteratedFDeriv ℝ j).self_of_nhds
    rw [h0]
    simp

/-- The uniform bound on the derivatives of the cutoff, as a function of the order. -/
def seeleyCutB (j : ℕ) : ℝ := Classical.choose (exists_seeleyCut_iteratedFDeriv_bound j)

lemma seeleyCutB_nonneg (j : ℕ) : 0 ≤ seeleyCutB j :=
  (Classical.choose_spec (exists_seeleyCut_iteratedFDeriv_bound j)).1

lemma norm_iteratedFDeriv_seeleyCut_le (j : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ j seeleyCut t‖ ≤ seeleyCutB j :=
  (Classical.choose_spec (exists_seeleyCut_iteratedFDeriv_bound j)).2 t

/-! ## The extension operator -/

/-- The cutoff factor on `X × ℝ`, as a complex valued function. -/
def seeleyChi (z : X × ℝ) : ℂ := (seeleyCut z.2 : ℂ)

/-- The `m`-th term of the Seeley sum. -/
def seeleyTerm (a b : ℕ → ℝ) (g : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) : ℂ :=
  (a m) • ((seeleyCut (-(b m) * p.2)) • g (p.1, -(b m) * p.2))

/-- The Seeley sum on the negative half space. -/
def seeleySum (a b : ℕ → ℝ) (g : X × ℝ → ℂ) (p : X × ℝ) : ℂ :=
  ∑' m, seeleyTerm a b g m p

/-- The Seeley extension of `g`. -/
def seeleyExt (a b : ℕ → ℝ) (g : X × ℝ → ℂ) (p : X × ℝ) : ℂ :=
  if 0 ≤ p.2 then g p else seeleySum a b g p

lemma seeleyExt_of_nonneg (a b : ℕ → ℝ) (g : X × ℝ → ℂ) {p : X × ℝ} (hp : 0 ≤ p.2) :
    seeleyExt a b g p = g p := if_pos hp

lemma seeleyExt_of_neg (a b : ℕ → ℝ) (g : X × ℝ → ℂ) {p : X × ℝ} (hp : p.2 < 0) :
    seeleyExt a b g p = seeleySum a b g p := if_neg (not_le.mpr hp)

lemma seeleyTerm_apply (a b : ℕ → ℝ) (g : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) :
    seeleyTerm a b g m p = (a m : ℂ) * ((seeleyCut (-(b m) * p.2) : ℂ) * g (p.1, -(b m) * p.2)) := by
  simp only [seeleyTerm, Complex.real_smul]

lemma seeleyTerm_add (a b : ℕ → ℝ) (g₁ g₂ : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) :
    seeleyTerm a b (g₁ + g₂) m p = seeleyTerm a b g₁ m p + seeleyTerm a b g₂ m p := by
  rw [seeleyTerm_apply, seeleyTerm_apply, seeleyTerm_apply, Pi.add_apply]
  ring

lemma seeleyTerm_smul (a b : ℕ → ℝ) (c : ℝ) (g : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) :
    seeleyTerm a b (c • g) m p = c • seeleyTerm a b g m p := by
  rw [seeleyTerm_apply, seeleyTerm_apply, Pi.smul_apply]
  rw [Complex.real_smul, Complex.real_smul]
  ring

lemma abs_neg_mul (x y : ℝ) : |-(x) * y| = |x| * |y| := by rw [abs_mul, abs_neg]

lemma exists_b_ge {b : ℕ → ℝ} (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (R : ℝ) :
    ∃ M : ℕ, ∀ m ≥ M, R ≤ b m := by
  have h : ∀ᶠ m in Filter.atTop, R ≤ b m := hbT.eventually (Filter.eventually_ge_atTop R)
  rcases Filter.eventually_atTop.mp h with ⟨M, hM⟩
  exact ⟨M, hM⟩

/-- For `p` in the negative half space only finitely many terms of the Seeley sum are non-zero. -/
lemma exists_finset_seeleyTerm_eq_zero {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (g : X × ℝ → ℂ) {p : X × ℝ} (hp : p.2 < 0) :
    ∃ S : Finset ℕ, ∀ m ∉ S, seeleyTerm a b g m p = 0 := by
  obtain ⟨M, hM⟩ := exists_b_ge hbT (2 / |p.2|)
  refine ⟨Finset.range M, fun m hm => ?_⟩
  simp only [Finset.mem_range, not_lt] at hm
  have hpabs : 0 < |p.2| := abs_pos.mpr (ne_of_lt hp)
  have hle : 2 / |p.2| ≤ b m := hM m hm
  have hge : 2 ≤ b m * |p.2| := by
    rw [div_le_iff₀ hpabs] at hle; linarith
  have harg : 2 ≤ |-(b m) * p.2| := by
    rw [abs_neg_mul, abs_of_nonneg (by linarith [hb m] : (0:ℝ) ≤ b m)]
    exact hge
  rw [seeleyTerm_apply, seeleyCut_eq_zero harg]
  simp

/-- On a whole neighbourhood of a point of the negative half space, the Seeley sum reduces to a
finite sum. -/
lemma eventuallyEq_finset_seeleySum {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (g : X × ℝ → ℂ) {p : X × ℝ} (hp : p.2 < 0) :
    ∃ S : Finset ℕ, seeleySum a b g =ᶠ[𝓝 p]
      (fun q => ∑ m ∈ S, seeleyTerm a b g m q) := by
  obtain ⟨M, hM⟩ := exists_b_ge hbT (2 / (-(p.2 / 2)))
  refine ⟨Finset.range M, ?_⟩
  have hp2 : p.2 < p.2 / 2 := by linarith
  have hneigh : {q : X × ℝ | q.2 < p.2 / 2} ∈ 𝓝 p :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hp2
  filter_upwards [hneigh] with q hq
  rw [seeleySum]
  symm
  rw [tsum_eq_sum]
  intro m hm
  simp only [Finset.mem_range, not_lt] at hm
  have hqabs : 0 < -(p.2 / 2) := by linarith
  have hle : 2 / (-(p.2 / 2)) ≤ b m := hM m hm
  have hge : 2 ≤ b m * (-(p.2 / 2)) := by
    rw [div_le_iff₀ hqabs] at hle; linarith
  have hqneg : q.2 < 0 := by linarith
  have harg : 2 ≤ |-(b m) * q.2| := by
    rw [abs_neg_mul, abs_of_nonneg (by linarith [hb m] : (0:ℝ) ≤ b m), abs_of_neg hqneg]
    nlinarith
  rw [seeleyTerm_apply, seeleyCut_eq_zero harg]
  simp

/-- The Seeley sum is additive in the function, on the negative half space. -/
lemma seeleySum_add {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (g₁ g₂ : X × ℝ → ℂ) {p : X × ℝ}
    (hp : p.2 < 0) :
    seeleySum a b (g₁ + g₂) p = seeleySum a b g₁ p + seeleySum a b g₂ p := by
  obtain ⟨S, hS⟩ := exists_finset_seeleyTerm_eq_zero hb hbT g₁ hp
  obtain ⟨S₂, hS₂⟩ := exists_finset_seeleyTerm_eq_zero hb hbT g₂ hp
  obtain ⟨S₃, hS₃⟩ := exists_finset_seeleyTerm_eq_zero hb hbT (g₁ + g₂) hp
  rw [seeleySum, seeleySum, seeleySum, tsum_eq_sum (s := S₃) hS₃, tsum_eq_sum (s := S) hS,
    tsum_eq_sum (s := S₂) hS₂]
  have e1 : (∑ m ∈ S₃, seeleyTerm a b (g₁ + g₂) m p)
      = ∑ m ∈ S₃ ∪ S ∪ S₂, seeleyTerm a b (g₁ + g₂) m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₃ m hm)
  have e2 : (∑ m ∈ S, seeleyTerm a b g₁ m p) = ∑ m ∈ S₃ ∪ S ∪ S₂, seeleyTerm a b g₁ m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS m hm)
  have e3 : (∑ m ∈ S₂, seeleyTerm a b g₂ m p) = ∑ m ∈ S₃ ∪ S ∪ S₂, seeleyTerm a b g₂ m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₂ m hm)
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => seeleyTerm_add a b g₁ g₂ m p

/-- The Seeley sum is homogeneous in the function, on the negative half space. -/
lemma seeleySum_smul {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (c : ℝ) (g : X × ℝ → ℂ) {p : X × ℝ}
    (hp : p.2 < 0) :
    seeleySum a b (c • g) p = c • seeleySum a b g p := by
  obtain ⟨S, hS⟩ := exists_finset_seeleyTerm_eq_zero hb hbT g hp
  obtain ⟨S₂, hS₂⟩ := exists_finset_seeleyTerm_eq_zero hb hbT (c • g) hp
  rw [seeleySum, seeleySum, tsum_eq_sum (s := S) hS, tsum_eq_sum (s := S₂) hS₂]
  have e1 : (∑ m ∈ S₂, seeleyTerm a b (c • g) m p) = ∑ m ∈ S₂ ∪ S, seeleyTerm a b (c • g) m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₂ m hm)
  have e2 : (∑ m ∈ S, seeleyTerm a b g m p) = ∑ m ∈ S₂ ∪ S, seeleyTerm a b g m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS m hm)
  rw [e1, e2, Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => seeleyTerm_smul a b c g m p

/-- The Seeley extension, as a linear map. -/
def seeleyLin (a b : ℕ → ℝ) (hb : ∀ m, 2 ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) :
    (X × ℝ → ℂ) →ₗ[ℝ] (X × ℝ → ℂ) where
  toFun := seeleyExt a b
  map_add' g₁ g₂ := by
    funext p
    by_cases hp : 0 ≤ p.2
    · rw [Pi.add_apply, seeleyExt_of_nonneg a b (g₁ + g₂) hp, seeleyExt_of_nonneg a b g₁ hp,
        seeleyExt_of_nonneg a b g₂ hp, Pi.add_apply]
    · have hp' : p.2 < 0 := lt_of_not_ge hp
      rw [Pi.add_apply, seeleyExt_of_neg a b (g₁ + g₂) hp', seeleyExt_of_neg a b g₁ hp',
        seeleyExt_of_neg a b g₂ hp', seeleySum_add hb hbT g₁ g₂ hp']
  map_smul' c g := by
    funext p
    by_cases hp : 0 ≤ p.2
    · rw [Pi.smul_apply, seeleyExt_of_nonneg a b (c • g) hp, seeleyExt_of_nonneg a b g hp,
        RingHom.id_apply, Pi.smul_apply]
    · have hp' : p.2 < 0 := lt_of_not_ge hp
      rw [Pi.smul_apply, seeleyExt_of_neg a b (c • g) hp', seeleyExt_of_neg a b g hp',
        RingHom.id_apply, seeleySum_smul hb hbT c g hp']

lemma seeleyLin_apply (a b : ℕ → ℝ) (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (g : X × ℝ → ℂ) : seeleyLin a b hb hbT g = seeleyExt a b g := rfl

end Work.NN.Final
