import Submission.Work.GYFactor6
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth
import Submission.Commons.Analysis.Complex.norm_inv_one_sub_le

/-!
# Green–Tao §10: continuity, holomorphy and bounds for the local factors `E^{(1)}, E^{(2)}, E^{(3)}`

This file supplies, for `F := G1u·G2u` (Green–Tao Lemma 10.3), the four hypotheses required by
`Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth` (Green–Tao Lemma 10.4) on the strip
`S = {z | -1/(6m) < Re z_j < 100}²`:
continuity of `uncurry F`, holomorphy along the coordinate lines, and a uniform bound.

The local factors `E1p`, `E2p`, `E3p` are built from expressions `n^w` (`n` a fixed positive
integer, `w` a linear function of the local datum) and inverses of `1 - n^{-(1+w)}`, so every
statement is proved in *composition* form: for arbitrary maps
`F₁ F₂ : α → Fin m → ℂ` into the local datum.  This covers at once the two-variable statements on
the strip and the one-variable statements along the coordinate lines `u ↦ Function.update z j u`
needed for the `DifferentiableAt` hypotheses.

## The region

On `Re z_j > -1/2` (and `Re z_j + Re z'_j > -1`) the factors `1 - n^{-(1+z_j)}` and
`1 - n^{-(1+z_j+z'_j)}` do not vanish, because `‖n^{-(1+w)}‖ = n^{-1-Re w} < 1` iff `Re w > -1`.
Our strip `Re z_j > -1/(6m)` lies well inside that region for `m ≥ 1`.
-/

open Finset Filter
open Commons.NumberTheory.Sieve
open scoped BigOperators Topology

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ} {W Amax : ℕ} {A : Fin m → Fin t → ℤ} {b : Fin m → ℤ}

/-! ## 1. The region `Re z_j, Re z'_j > c` -/

/-- The open region of pairs `(z,z')` with `Re z_j, Re z'_j > c`. -/
def goodRegion (m : ℕ) (c : ℝ) : Set ((Fin m → ℂ) × (Fin m → ℂ)) :=
  {x | (∀ j, c < (x.1 j).re) ∧ (∀ j, c < (x.2 j).re)}

lemma isOpen_goodRegion (m : ℕ) (c : ℝ) : IsOpen (goodRegion m c) := by
  have h1 : IsOpen {z : Fin m → ℂ | ∀ j, c < (z j).re} := by
    rw [show {z : Fin m → ℂ | ∀ j, c < (z j).re} = ⋂ j, {z : Fin m → ℂ | c < (z j).re} by
      ext z; simp]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply j))
  exact (h1.preimage continuous_fst).inter (h1.preimage continuous_snd)

lemma mem_goodRegion {c : ℝ} {x : (Fin m → ℂ) × (Fin m → ℂ)} :
    x ∈ goodRegion m c ↔ (∀ j, c < (x.1 j).re) ∧ (∀ j, c < (x.2 j).re) := Iff.rfl

/-! ## 2. Finite products and sums of `ContinuousOn` functions -/

lemma continuousOn_finsetProd' {α : Type*} [TopologicalSpace α] {ι : Type*} {s : Set α}
    {f : ι → α → ℂ} (u : Finset ι) (h : ∀ i ∈ u, ContinuousOn (f i) s) :
    ContinuousOn (fun a => ∏ i ∈ u, f i a) s := by
  classical
  induction u using Finset.induction with
  | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : α => (1 : ℂ)) s)
  | insert d v hd ih =>
      have h1 : ContinuousOn (f d * fun a => ∏ i ∈ v, f i a) s :=
        (h d (Finset.mem_insert_self d v)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine h1.congr fun a _ => ?_
      simp only [Pi.mul_apply, Finset.prod_insert hd]

lemma continuousOn_finsetSum' {α : Type*} [TopologicalSpace α] {ι : Type*} {s : Set α}
    {f : ι → α → ℂ} (u : Finset ι) (h : ∀ i ∈ u, ContinuousOn (f i) s) :
    ContinuousOn (fun a => ∑ i ∈ u, f i a) s := by
  classical
  induction u using Finset.induction with
  | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : α => (0 : ℂ)) s)
  | insert d v hd ih =>
      have h1 : ContinuousOn (f d + fun a => ∑ i ∈ v, f i a) s :=
        (h d (Finset.mem_insert_self d v)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine h1.congr fun a _ => ?_
      simp only [Pi.add_apply, Finset.sum_insert hd]

/-! ## 3. Non-vanishing of `1 - n^{-(1+w)}` on the region -/

/-- `n^{-(1+z)} ≠ 1` when `Re z > -1/2` and `n` is prime. -/
lemma cpow_ne_one {n : ℕ} (hn : n.Prime) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    (n : ℂ) ^ (-(1 + z)) ≠ 1 := by
  intro h
  have h1 := cpow_neg_one_sub_lt_one (p := n) hn.two_le (c := -(1 / 2 : ℝ))
    (by norm_num) (le_of_lt hz)
  rw [h, norm_one] at h1
  exact lt_irrefl 1 h1

/-- `n^{-(1+z+z')} ≠ 1` when `Re z, Re z' > -1/2` and `n` is prime. -/
lemma cpow_sum_ne_one {n : ℕ} (hn : n.Prime) {z z' : ℂ}
    (hz : -(1 / 2 : ℝ) < z.re) (hz' : -(1 / 2 : ℝ) < z'.re) :
    (n : ℂ) ^ (-(1 + z + z')) ≠ 1 := by
  intro h
  have hc : -1 < (z.re + z'.re - 1) / 2 := by linarith
  have hzle : (z.re + z'.re - 1) / 2 ≤ (z + z').re := by
    rw [Complex.add_re]; linarith
  have h1 := cpow_neg_one_sub_lt_one (p := n) hn.two_le hc hzle
  rw [show -(1 + (z + z')) = -(1 + z + z') by ring] at h1
  rw [h, norm_one] at h1
  exact lt_irrefl 1 h1

/-- `E3p` does not vanish on the region `Re > -1/2`. -/
lemma E3p_ne_zero_of_re {n : ℕ} (hn : n.Prime) {F₁ F₂ : Fin m → ℂ}
    (h : ∀ i, -(1 / 2 : ℝ) < (F₁ i).re ∧ -(1 / 2 : ℝ) < (F₂ i).re) :
    E3p F₁ F₂ n ≠ 0 := by
  rw [E3p, if_pos hn]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact sub_ne_zero.mpr (Ne.symm (cpow_ne_one hn (h j).1))
  · exact sub_ne_zero.mpr (Ne.symm (cpow_ne_one hn (h j).2))
  · exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm (cpow_sum_ne_one hn (h j).1 (h j).2)))

/-! ## 4. Continuity of the local factors, in composition form -/

/-- `eulerFactor` is continuous in the local datum when the base `n` is nonzero. -/
lemma continuous_eulerFactor_comp {α : Type*} [TopologicalSpace α] {n : ℕ} (hn : (n : ℂ) ≠ 0)
    {F₁ F₂ : α → Fin m → ℂ} (h₁ : ∀ i, Continuous fun a => F₁ a i)
    (h₂ : ∀ i, Continuous fun a => F₂ a i) :
    Continuous fun a => eulerFactor m (vSys W A b) (F₁ a) (F₂ a) n := by
  simp only [eulerFactor]
  refine continuous_finsetSum _ fun σ _ => ?_
  have hp1 : Continuous fun a : α => ∏ i ∈ σ.X, (n : ℂ) ^ (-(F₁ a i)) :=
    continuous_finsetProd _ fun i _ => (h₁ i).neg.const_cpow (Or.inl hn)
  have hp2 : Continuous fun a : α => ∏ i ∈ σ.X', (n : ℂ) ^ (-(F₂ a i)) :=
    continuous_finsetProd _ fun i _ => (h₂ i).neg.const_cpow (Or.inl hn)
  exact (continuous_const.mul continuous_const).mul (hp1.mul hp2)

lemma continuousOn_eulerFactor_comp {α : Type*} [TopologicalSpace α] {s : Set α} {n : ℕ}
    (hn : (n : ℂ) ≠ 0) {F₁ F₂ : α → Fin m → ℂ}
    (h₁ : ∀ i, ContinuousOn (fun a => F₁ a i) s)
    (h₂ : ∀ i, ContinuousOn (fun a => F₂ a i) s) :
    ContinuousOn (fun a => eulerFactor m (vSys W A b) (F₁ a) (F₂ a) n) s := by
  simp only [eulerFactor]
  refine continuousOn_finsetSum' _ fun σ _ => ?_
  have hp1 : ContinuousOn (fun a : α => ∏ i ∈ σ.X, (n : ℂ) ^ (-(F₁ a i))) s :=
    continuousOn_finsetProd' _ fun i _ => (h₁ i).neg.const_cpow (Or.inl hn)
  have hp2 : ContinuousOn (fun a : α => ∏ i ∈ σ.X', (n : ℂ) ^ (-(F₂ a i))) s :=
    continuousOn_finsetProd' _ fun i _ => (h₂ i).neg.const_cpow (Or.inl hn)
  exact (continuousOn_const.mul continuousOn_const).mul (hp1.mul hp2)

/-- Continuity of `E3p` in the local datum on the region `Re > -1/2`. -/
lemma continuousOn_E3p_comp {α : Type*} [TopologicalSpace α] {s : Set α} {n : ℕ} (hn : n.Prime)
    {F₁ F₂ : α → Fin m → ℂ} (h₁ : ∀ i, ContinuousOn (fun a => F₁ a i) s)
    (h₂ : ∀ i, ContinuousOn (fun a => F₂ a i) s)
    (hs : ∀ a ∈ s, ∀ i, -(1 / 2 : ℝ) < (F₁ a i).re ∧ -(1 / 2 : ℝ) < (F₂ a i).re) :
    ContinuousOn (fun a => E3p (F₁ a) (F₂ a) n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  simp only [E3p, if_pos hn]
  refine continuousOn_finsetProd' _ fun j _ => ?_
  have hA : ContinuousOn (fun a => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ a j))) s :=
    continuousOn_const.sub ((continuousOn_const.add (h₁ j)).neg.const_cpow (Or.inl hn0))
  have hB : ContinuousOn (fun a => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₂ a j))) s :=
    continuousOn_const.sub ((continuousOn_const.add (h₂ j)).neg.const_cpow (Or.inl hn0))
  have hC : ContinuousOn (fun a => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ a j + F₂ a j))) s :=
    continuousOn_const.sub (((continuousOn_const.add (h₁ j)).add (h₂ j)).neg.const_cpow (Or.inl hn0))
  exact (hA.mul hB).mul (hC.inv₀ fun a ha => sub_ne_zero.mpr
    (Ne.symm (cpow_sum_ne_one hn ((hs a ha) j).1 ((hs a ha) j).2)))

/-- Continuity of `E2p` in the local datum on the region `Re > -1/2`. -/
lemma continuousOn_E2p_comp {α : Type*} [TopologicalSpace α] {s : Set α} {n : ℕ} (hn : n.Prime)
    {F₁ F₂ : α → Fin m → ℂ} (h₁ : ∀ i, ContinuousOn (fun a => F₁ a i) s)
    (h₂ : ∀ i, ContinuousOn (fun a => F₂ a i) s)
    (hs : ∀ a ∈ s, ∀ i, -(1 / 2 : ℝ) < (F₁ a i).re ∧ -(1 / 2 : ℝ) < (F₂ a i).re) :
    ContinuousOn (fun a => E2p W (F₁ a) (F₂ a) n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  by_cases hW : n ∣ W
  · simp only [E2p, if_pos (show n.Prime ∧ n ∣ W from ⟨hn, hW⟩)]
    refine continuousOn_finsetProd' _ fun j _ => ?_
    have hA : ContinuousOn (fun a => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ a j))) s :=
      continuousOn_const.sub ((continuousOn_const.add (h₁ j)).neg.const_cpow (Or.inl hn0))
    have hB : ContinuousOn (fun a => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₂ a j))) s :=
      continuousOn_const.sub ((continuousOn_const.add (h₂ j)).neg.const_cpow (Or.inl hn0))
    have hC : ContinuousOn (fun a => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ a j + F₂ a j))) s :=
      continuousOn_const.sub
        (((continuousOn_const.add (h₁ j)).add (h₂ j)).neg.const_cpow (Or.inl hn0))
    exact ((hA.inv₀ (fun a ha => sub_ne_zero.mpr
        (Ne.symm (cpow_ne_one hn ((hs a ha) j).1)))).mul
      (hB.inv₀ (fun a ha => sub_ne_zero.mpr
        (Ne.symm (cpow_ne_one hn ((hs a ha) j).2))))).mul hC
  · simp only [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hW hc.2)]
    exact continuousOn_const

/-- Continuity of `E1p` in the local datum on the region `Re > -1/2`. -/
lemma continuousOn_E1p_comp {α : Type*} [TopologicalSpace α] {s : Set α} {n : ℕ} (hn : n.Prime)
    {F₁ F₂ : α → Fin m → ℂ} (h₁ : ∀ i, ContinuousOn (fun a => F₁ a i) s)
    (h₂ : ∀ i, ContinuousOn (fun a => F₂ a i) s)
    (hs : ∀ a ∈ s, ∀ i, -(1 / 2 : ℝ) < (F₁ a i).re ∧ -(1 / 2 : ℝ) < (F₂ a i).re) :
    ContinuousOn (fun a => E1p W A b (F₁ a) (F₂ a) n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  by_cases hW : n ∣ W
  · simp only [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 hW)]
    exact continuousOn_const
  · simp only [E1p, if_pos (show n.Prime ∧ ¬ n ∣ W from ⟨hn, hW⟩)]
    exact (continuousOn_eulerFactor_comp (W := W) (A := A) (b := b) hn0 h₁ h₂).div
      (continuousOn_E3p_comp hn h₁ h₂ hs) (fun a ha => E3p_ne_zero_of_re hn (hs a ha))

/-! ## 5. Holomorphy of the local factors, in composition form -/

lemma differentiableOn_finsetProd' {s : Set ℂ} {ι : Type*} {f : ι → ℂ → ℂ} (u : Finset ι)
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun a => ∏ i ∈ u, f i a) s := by
  classical
  induction u using Finset.induction with
  | empty =>
      exact (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s)
  | insert d v hd ih =>
      have h1 : DifferentiableOn ℂ (f d * fun a => ∏ i ∈ v, f i a) s :=
        (h d (Finset.mem_insert_self d v)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine h1.congr fun a _ => ?_
      simp only [Pi.mul_apply, Finset.prod_insert hd]

/-- `eulerFactor` is holomorphic in the local datum along any holomorphic curve. -/
lemma differentiableOn_eulerFactor_comp {s : Set ℂ} {n : ℕ} (hn : (n : ℂ) ≠ 0)
    {F₁ F₂ : ℂ → Fin m → ℂ} (h₁ : ∀ i, DifferentiableOn ℂ (fun u => F₁ u i) s)
    (h₂ : ∀ i, DifferentiableOn ℂ (fun u => F₂ u i) s) :
    DifferentiableOn ℂ (fun u => eulerFactor m (vSys W A b) (F₁ u) (F₂ u) n) s := by
  simp only [eulerFactor]
  refine DifferentiableOn.fun_sum (u := Finset.univ) fun σ _ => ?_
  have hp1 : DifferentiableOn ℂ (fun u : ℂ => ∏ i ∈ σ.X, (n : ℂ) ^ (-(F₁ u i))) s :=
    differentiableOn_finsetProd' σ.X fun i _ => (h₁ i).neg.const_cpow (Or.inl hn)
  have hp2 : DifferentiableOn ℂ (fun u : ℂ => ∏ i ∈ σ.X', (n : ℂ) ^ (-(F₂ u i))) s :=
    differentiableOn_finsetProd' σ.X' fun i _ => (h₂ i).neg.const_cpow (Or.inl hn)
  refine ((differentiableOn_const (c := vSys W A b n σ) : DifferentiableOn ℂ (fun _ : ℂ => vSys W A b n σ) s).mul
    (differentiableOn_const (c := ((-1 : ℂ) ^ (σ.X.card + σ.X'.card))) : DifferentiableOn ℂ (fun _ : ℂ => ((-1 : ℂ) ^ (σ.X.card + σ.X'.card))) s)).mul
    (hp1.mul hp2) |>.congr fun u _ => ?_
  simp only [Pi.mul_apply]

/-- Holomorphy of `E3p` in the local datum on the region `Re > -1/2`. -/
lemma differentiableOn_E3p_comp {s : Set ℂ} {n : ℕ} (hn : n.Prime)
    {F₁ F₂ : ℂ → Fin m → ℂ} (h₁ : ∀ i, DifferentiableOn ℂ (fun u => F₁ u i) s)
    (h₂ : ∀ i, DifferentiableOn ℂ (fun u => F₂ u i) s)
    (hs : ∀ u ∈ s, ∀ i, -(1 / 2 : ℝ) < (F₁ u i).re ∧ -(1 / 2 : ℝ) < (F₂ u i).re) :
    DifferentiableOn ℂ (fun u => E3p (F₁ u) (F₂ u) n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  simp only [E3p, if_pos hn]
  refine differentiableOn_finsetProd' _ fun j _ => ?_
  have hA : DifferentiableOn ℂ (fun u => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ u j))) s :=
    (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).sub (((differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).add (h₁ j)).neg.const_cpow (Or.inl hn0))
  have hB : DifferentiableOn ℂ (fun u => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₂ u j))) s :=
    (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).sub (((differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).add (h₂ j)).neg.const_cpow (Or.inl hn0))
  have hC : DifferentiableOn ℂ (fun u => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ u j + F₂ u j))) s :=
    (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).sub
      ((((differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).add (h₁ j)).add (h₂ j)).neg.const_cpow (Or.inl hn0))
  exact (hA.mul hB).mul (hC.inv fun u hu => sub_ne_zero.mpr
    (Ne.symm (cpow_sum_ne_one hn ((hs u hu) j).1 ((hs u hu) j).2)))

/-- Holomorphy of `E2p` in the local datum on the region `Re > -1/2`. -/
lemma differentiableOn_E2p_comp {s : Set ℂ} {n : ℕ} (hn : n.Prime)
    {F₁ F₂ : ℂ → Fin m → ℂ} (h₁ : ∀ i, DifferentiableOn ℂ (fun u => F₁ u i) s)
    (h₂ : ∀ i, DifferentiableOn ℂ (fun u => F₂ u i) s)
    (hs : ∀ u ∈ s, ∀ i, -(1 / 2 : ℝ) < (F₁ u i).re ∧ -(1 / 2 : ℝ) < (F₂ u i).re) :
    DifferentiableOn ℂ (fun u => E2p W (F₁ u) (F₂ u) n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  by_cases hW : n ∣ W
  · simp only [E2p, if_pos (show n.Prime ∧ n ∣ W from ⟨hn, hW⟩)]
    refine differentiableOn_finsetProd' _ fun j _ => ?_
    have hA : DifferentiableOn ℂ (fun u => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ u j))) s :=
      (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).sub (((differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).add (h₁ j)).neg.const_cpow (Or.inl hn0))
    have hB : DifferentiableOn ℂ (fun u => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₂ u j))) s :=
      (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).sub (((differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).add (h₂ j)).neg.const_cpow (Or.inl hn0))
    have hC : DifferentiableOn ℂ (fun u => (1 : ℂ) - (n : ℂ) ^ (-(1 + F₁ u j + F₂ u j))) s :=
      (differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).sub
        ((((differentiableOn_const (c := (1 : ℂ)) : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s).add (h₁ j)).add (h₂ j)).neg.const_cpow (Or.inl hn0))
    exact (((hA.inv fun u hu => sub_ne_zero.mpr
        (Ne.symm (cpow_ne_one hn ((hs u hu) j).1)))).mul
      (hB.inv fun u hu => sub_ne_zero.mpr
        (Ne.symm (cpow_ne_one hn ((hs u hu) j).2)))) |>.mul hC
  · simp only [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hW hc.2)]
    exact differentiableOn_const (c := (1 : ℂ))

/-- Holomorphy of `E1p` in the local datum on the region `Re > -1/2`. -/
lemma differentiableOn_E1p_comp {s : Set ℂ} {n : ℕ} (hn : n.Prime)
    {F₁ F₂ : ℂ → Fin m → ℂ} (h₁ : ∀ i, DifferentiableOn ℂ (fun u => F₁ u i) s)
    (h₂ : ∀ i, DifferentiableOn ℂ (fun u => F₂ u i) s)
    (hs : ∀ u ∈ s, ∀ i, -(1 / 2 : ℝ) < (F₁ u i).re ∧ -(1 / 2 : ℝ) < (F₂ u i).re) :
    DifferentiableOn ℂ (fun u => E1p W A b (F₁ u) (F₂ u) n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  by_cases hW : n ∣ W
  · simp only [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 hW)]
    exact differentiableOn_const (c := (1 : ℂ))
  · simp only [E1p, if_pos (show n.Prime ∧ ¬ n ∣ W from ⟨hn, hW⟩)]
    exact (differentiableOn_eulerFactor_comp (s := s) (W := W) (A := A) (b := b) hn0 h₁ h₂).div
      (differentiableOn_E3p_comp (s := s) hn h₁ h₂ hs) (fun u hu => E3p_ne_zero_of_re hn (hs u hu))

/-! ## 6. The majorant of `E_p^{(1)} - 1` on the strip

For a prime `n ∤ W`, Green–Tao Lemma 10.3 (`E1p_bound`) gives
`E_n^{(1)} - 1 = O_m(n^{-2+2σ₀m} + n^{-2+4σ₀})` **provided** `m(2n^{-1+σ₀} + n^{-1+2σ₀}) ≤ 1/2`, which
fails only for the finitely many primes `n < (6m)²+2`.  For those we supply a crude bound, valid
for every `n ∤ W` on the strip: `‖E_n^{(1)}‖ ≤ 2·4^m·28^m` (the `eulerFactor` expansion gives
`‖E_n‖ ≤ 2·4^m`, while `‖(E_n^{(3)})^{-1}‖ ≤ 28^m` because `‖n^{-1-w}‖ ≤ 2^{-1/2} ≤ 3/4` on the
strip).
-/

/-- `2^{-1/2} ≤ 3/4`. -/
lemma two_rpow_neg_half_le : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
  have h2 : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0 : ℝ) < ((2 : ℝ) ^ (-(1 / 2 : ℝ)) + 3 / 4)
      * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) - 3 / 4) := by
    apply mul_pos <;> linarith
  nlinarith [h2, h3]

/-- On the strip, `‖n^{-(1+w)}‖ ≤ 3/4` for `n ≥ 2` and `Re w ≥ -1/2`. -/
lemma norm_cpow_le_three_quarters {n : ℕ} (hn : 2 ≤ n) {w : ℂ}
    (hw : -(1 / 2 : ℝ) ≤ w.re) : ‖(n : ℂ) ^ (-(1 + w))‖ ≤ 3 / 4 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : ‖(n : ℂ) ^ (-(1 + w))‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have h := norm_cpow_neg_one_sub_le (p := n) (by omega : 1 ≤ n) (c := -(1 / 2 : ℝ)) hw
    rwa [show -1 - -(1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] at h
  have h2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by norm_num)
  exact le_trans h1 (le_trans h2 two_rpow_neg_half_le)

/-- `-1/2 ≤ -1/(6m)` for `m ≥ 1`. -/
lemma neg_half_le_neg_inv (m : ℕ) (hm : 1 ≤ m) :
    -(1 / 2 : ℝ) ≤ -(1 / (6 * (m : ℝ))) := by
  rw [neg_le_neg_iff]
  refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ?_
  have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- The crude bound `‖(E_n^{(3)})^{-1}‖ ≤ 28^m` on the strip. -/
lemma E3p_inv_le {n m : ℕ} (hn : n.Prime) (hm : 1 ≤ m) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖(E3p z z' n)⁻¹‖ ≤ (28 : ℝ) ^ m := by
  have hn2 : 2 ≤ n := hn.two_le
  have hperj : ∀ j : Fin m, (1 / 28 : ℝ) ≤
      ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j))) * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))⁻¹‖ := by
    intro j
    have hmm := neg_half_le_neg_inv m hm
    have hzj : -(1 / 2 : ℝ) ≤ (z j).re := le_trans hmm (hz j)
    have hzj' : -(1 / 2 : ℝ) ≤ (z' j).re := le_trans hmm (hz' j)
    have hsum : -(1 / 2 : ℝ) ≤ (z j + z' j).re := by
      rw [Complex.add_re]
      have h2 : -(2 * (1 / (6 * (m : ℝ)))) ≤ (z j).re + (z' j).re := by
        linarith [hz j, hz' j]
      have hpos : (0 : ℝ) < 6 * (m : ℝ) := by
        have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hB : -(1 / 2 : ℝ) ≤ -(2 * (1 / (6 * (m : ℝ)))) := by
        rw [neg_le_neg_iff]
        rw [show 2 * (1 / (6 * (m : ℝ))) = 2 / (6 * (m : ℝ)) by ring, div_le_iff₀ hpos]
        have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      linarith
    have h3 : ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))) ≠ 0 := by
      intro hcon
      have hw : (n : ℂ) ^ (-(1 + (z j + z' j))) = 1 := by
        have h0 : (n : ℂ) ^ (-(1 + z j + z' j)) = 1 := (sub_eq_zero.mp hcon).symm
        rwa [show (-(1 + z j + z' j) : ℂ) = -(1 + (z j + z' j)) by ring] at h0
      have hle := norm_cpow_le_three_quarters hn2 hsum
      rw [hw, norm_one] at hle
      norm_num at hle
    have hA : (1 / 4 : ℝ) ≤ ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z j))‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((n : ℂ) ^ (-(1 + z j)))
      rw [norm_one] at h
      have h2 := norm_cpow_le_three_quarters hn2 hzj
      linarith
    have hB : (1 / 4 : ℝ) ≤ ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z' j))‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((n : ℂ) ^ (-(1 + z' j)))
      rw [norm_one] at h
      have h2 := norm_cpow_le_three_quarters hn2 hzj'
      linarith
    have hC : (4 / 7 : ℝ) ≤ (‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖)⁻¹ := by
      have h4 : ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖ ≤ 7 / 4 := by
        have h := norm_sub_le (1 : ℂ) ((n : ℂ) ^ (-(1 + z j + z' j)))
        rw [norm_one] at h
        have h2 : ‖(n : ℂ) ^ (-(1 + z j + z' j))‖ ≤ 3 / 4 := by
          have h3 := norm_cpow_le_three_quarters hn2 hsum
          rwa [show (-(1 + (z j + z' j)) : ℂ) = -(1 + z j + z' j) by ring] at h3
        linarith
      have hpos : (0 : ℝ) < ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖ := by
        rw [norm_pos_iff]; exact h3
      calc (4 / 7 : ℝ) = ((7 / 4 : ℝ))⁻¹ := by norm_num
        _ ≤ (‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖)⁻¹ :=
            (inv_le_inv₀ (by norm_num) hpos).mpr h4
    rw [norm_mul, norm_mul, norm_inv]
    calc (1 / 28 : ℝ) = (1 / 4) * (1 / 4) * (4 / 7) := by norm_num
      _ ≤ ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z j))‖ * ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z' j))‖
            * (‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖)⁻¹ :=
          mul_le_mul (mul_le_mul hA hB (by norm_num) (norm_nonneg _)) hC
            (by norm_num) (by positivity)
  have hnorm : (1 / 28 : ℝ) ^ m ≤ ‖E3p z z' n‖ := by
    rw [E3p, if_pos hn, norm_prod]
    have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin m => (1 / 28 : ℝ))
      (g := fun j => ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j))) * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))⁻¹‖)
      (fun j _ => by norm_num) (fun j _ => hperj j)
    simpa [Finset.prod_const, Finset.card_univ] using h
  rw [norm_inv]
  have hpos28 : (0 : ℝ) < (1 / 28 : ℝ) ^ m := by positivity
  have hposn : (0 : ℝ) < ‖E3p z z' n‖ := lt_of_lt_of_le hpos28 hnorm
  calc (‖E3p z z' n‖)⁻¹ ≤ ((1 / 28 : ℝ) ^ m)⁻¹ := (inv_le_inv₀ hposn hpos28).mpr hnorm
    _ = (28 : ℝ) ^ m := by rw [div_pow, one_pow, one_div, inv_inv]

/-- `(3m+1) ≤ 4^m` for `m ≥ 1`. -/
lemma three_mul_add_one_le_four_pow (m : ℕ) (hm : 1 ≤ m) : 3 * m + 1 ≤ 4 ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; norm_num
      · have ih' := ih (by omega)
        have hge : 4 ≤ 4 ^ k := by
          calc (4 : ℕ) = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        calc 3 * (k + 1) + 1 = 3 * k + 4 := by ring
          _ ≤ 4 ^ k + 4 := by omega
          _ ≤ 4 ^ k + 4 ^ k := by omega
          _ = 2 * 4 ^ k := by ring
          _ ≤ 4 * 4 ^ k := by omega
          _ = 4 ^ (k + 1) := by ring

/-- The crude bound `‖E_n‖ ≤ 2·4^m` for the Euler factor on the strip. -/
lemma norm_eulerFactor_le (H : LocHyp W Amax A b) {n : ℕ} (hn : n.Prime) (hnW : ¬ n ∣ W)
    {z z' : Fin m → ℂ} (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖eulerFactor m (vSys W A b) z z' n‖ ≤ 2 * (4 : ℝ) ^ m := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.one_le
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hσ0 : (0 : ℝ) ≤ 1 / (6 * (m : ℝ)) := by positivity
  have hσle : 1 / (6 * (m : ℝ)) ≤ 1 / 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ 6 * (m : ℝ))
  obtain ⟨R, hR, hReq⟩ := eulerFactor_expansion H hn hnW hσ0 hz hz'
  have hexp1 : -2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ) ≤ 0 := by
    have h : 2 * (1 / (6 * (m : ℝ))) * (m : ℝ) = 1 / 3 := by field_simp; ring
    rw [h]; norm_num
  have hexp2 : -2 + 4 * (1 / (6 * (m : ℝ))) ≤ 0 := by
    have h : 4 * (1 / (6 * (m : ℝ))) = 2 / (3 * (m : ℝ)) := by ring
    have h2 : (2 : ℝ) / (3 * (m : ℝ)) ≤ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (m : ℝ))]
      linarith
    linarith
  have hRle : ‖R‖ ≤ (4 : ℝ) ^ m := by
    refine le_trans hR (mul_le_of_le_one_right (by positivity) ?_)
    have h1 : (n : ℝ) ^ (-2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hn1 hexp1
      rwa [Real.rpow_zero] at h
    have h2 : (n : ℝ) ^ (-2 + 4 * (1 / (6 * (m : ℝ)))) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hn1 hexp2
      rwa [Real.rpow_zero] at h
    linarith
  have hL : ‖eLin z z' n‖ ≤ 3 * (m : ℝ) := by
    have h := norm_eLin_le (m := m) (p := n) hn.one_le (σ₀ := 1 / (6 * (m : ℝ))) hz hz'
    have h1 : (n : ℝ) ^ (-1 + 1 / (6 * (m : ℝ))) ≤ 1 := by
      have hexp : -1 + 1 / (6 * (m : ℝ)) ≤ 0 := by linarith
      have h2 := Real.rpow_le_rpow_of_exponent_le hn1 hexp
      rwa [Real.rpow_zero] at h2
    have h2 : (n : ℝ) ^ (-1 + 2 * (1 / (6 * (m : ℝ)))) ≤ 1 := by
      have hexp : -1 + 2 * (1 / (6 * (m : ℝ))) ≤ 0 := by linarith
      have h2 := Real.rpow_le_rpow_of_exponent_le hn1 hexp
      rwa [Real.rpow_zero] at h2
    nlinarith [h, h1, h2, hmpos]
  have htri : ‖eulerFactor m (vSys W A b) z z' n‖ ≤ 1 + ‖eLin z z' n‖ + ‖R‖ := by
    rw [hReq]
    have h := norm_add_le ((1 : ℂ) - eLin z z' n) R
    have h2 : ‖(1 : ℂ) - eLin z z' n‖ ≤ 1 + ‖eLin z z' n‖ := by
      have h3 := norm_sub_le (1 : ℂ) (eLin z z' n)
      rwa [norm_one] at h3
    linarith
  have hfinal : 1 + 3 * (m : ℝ) + (4 : ℝ) ^ m ≤ 2 * (4 : ℝ) ^ m := by
    have h := three_mul_add_one_le_four_pow m H.hm
    have h' : (3 : ℝ) * (m : ℝ) + 1 ≤ (4 : ℝ) ^ m := by exact_mod_cast h
    linarith
  linarith [htri, hL, hRle, hfinal]

/-- The crude bound `‖E_n^{(1)} - 1‖ ≤ 2·4^m·28^m + 1` on the strip. -/
lemma E1p_crude (H : LocHyp W Amax A b) {n : ℕ} (hn : n.Prime) (hnW : ¬ n ∣ W)
    {z z' : Fin m → ℂ} (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E1p W A b z z' n - 1‖ ≤ 2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m + 1 := by
  have h1 : ‖E1p W A b z z' n‖ ≤ 2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m := by
    rw [E1p, if_pos (show n.Prime ∧ ¬ n ∣ W from ⟨hn, hnW⟩), div_eq_mul_inv, norm_mul, norm_inv,
      ← norm_inv]
    calc ‖eulerFactor m (vSys W A b) z z' n‖ * ‖(E3p z z' n)⁻¹‖
        ≤ (2 * (4 : ℝ) ^ m) * (28 : ℝ) ^ m :=
          mul_le_mul (norm_eulerFactor_le H hn hnW hz hz') (E3p_inv_le hn H.hm hz hz')
            (norm_nonneg _) (by positivity)
      _ = 2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m := by ring
  have h2 := norm_sub_le (E1p W A b z z' n) (1 : ℂ)
  rw [norm_one] at h2
  linarith

/-- The majorant of Green–Tao Lemma 10.3. -/
noncomputable def cpowMajor (m : ℕ) : ℕ → ℝ := fun n =>
  100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
    * ((n : ℝ) ^ (-2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ))
        + (n : ℝ) ^ (-2 + 4 * (1 / (6 * (m : ℝ)))))

/-- The global majorant of `‖E_n^{(1)} - 1‖` on the strip: Green–Tao's bound plus a finite
correction for the primes below the threshold `(6m)²+2`. -/
noncomputable def e1pMajor (m : ℕ) : ℕ → ℝ := fun n =>
  cpowMajor m n + (if n ≤ (6 * m) ^ 2 + 2 then 2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m + 1 else 0)

lemma summable_cpowMajor {m : ℕ} (hm : 1 ≤ m) : Summable (cpowMajor m) := by
  have h := summable_E1p_major (m := m) (σ₀ := 1 / (6 * (m : ℝ)))
    (sixth_small hm).1 (sixth_small hm).2
  change Summable (fun p : ℕ => 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
    * ((p : ℝ) ^ (-2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ))
        + (p : ℝ) ^ (-2 + 4 * (1 / (6 * (m : ℝ))))))
  exact h

lemma summable_e1pMajor {m : ℕ} (hm : 1 ≤ m) : Summable (e1pMajor m) := by
  change Summable (fun n : ℕ => cpowMajor m n
    + (if n ≤ (6 * m) ^ 2 + 2 then 2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m + 1 else 0))
  refine (summable_cpowMajor hm).add ?_
  refine Summable.of_norm_bounded_eventually_nat
    (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) ?_
  rw [Filter.eventually_atTop]
  refine ⟨(6 * m) ^ 2 + 3, fun n hn => ?_⟩
  have h : ¬ (n ≤ (6 * m) ^ 2 + 2) := by omega
  simp [h]

/-- **Green–Tao Lemma 10.3, uniform form**: the `E^{(1)}` remainder is dominated on the whole
strip by the summable majorant `e1pMajor m`. -/
lemma E1p_sub_one_le_major (H : LocHyp W Amax A b) {n : ℕ} (hn : n.Prime) (hnW : ¬ n ∣ W)
    {z z' : Fin m → ℂ} (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E1p W A b z z' n - 1‖ ≤ e1pMajor m n := by
  by_cases hsmall : (m : ℝ) * (2 * (n : ℝ) ^ (-1 + 1 / (6 * (m : ℝ)))
      + (n : ℝ) ^ (-1 + 2 * (1 / (6 * (m : ℝ))))) ≤ 1 / 2
  · have hb := E1p_bound H hn hnW (by positivity) (le_of_lt (sixth_small H.hm).1) hz hz' hsmall
    refine le_trans hb ?_
    unfold e1pMajor cpowMajor
    refine le_add_of_nonneg_right ?_
    by_cases h : n ≤ (6 * m) ^ 2 + 2
    · simp only [if_pos h]; positivity
    · simp [if_neg h]
  · have hnK : n ≤ (6 * m) ^ 2 + 2 := by
      by_contra hcon
      exact hsmall (hsmall_of_large (σ₀ := 1 / (6 * (m : ℝ))) (by positivity)
        (le_of_lt (sixth_small H.hm).1) H.hm (by omega))
    rw [show e1pMajor m n = cpowMajor m n + (2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m + 1) by
      unfold e1pMajor; rw [if_pos hnK]]
    calc ‖E1p W A b z z' n - 1‖ ≤ 2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m + 1 := E1p_crude H hn hnW hz hz'
      _ ≤ cpowMajor m n + (2 * (4 : ℝ) ^ m * (28 : ℝ) ^ m + 1) :=
          le_add_of_nonneg_left (by unfold cpowMajor; positivity)

/-! ## 7. `G₁ = ∏_p E_p^{(1)}` and `G₂ = ∏_p E_p^{(2)}` on the strip -/

/-- `-1/2 < -1/(6m)` for `m ≥ 1`. -/
lemma neg_half_lt_neg_inv_six {m : ℕ} (hm : 1 ≤ m) : -(1 / 2 : ℝ) < -(1 / (6 * (m : ℝ))) := by
  rw [neg_lt_neg_iff]
  refine one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) ?_
  have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- Coordinate projections are continuous on any `goodRegion`. -/
lemma continuousOn_fst_coord (c : ℝ) (i : Fin m) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => x.1 i) (goodRegion m c) :=
  ((continuous_apply i).comp continuous_fst).continuousOn.mono (Set.subset_univ _)

lemma continuousOn_snd_coord (c : ℝ) (i : Fin m) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => x.2 i) (goodRegion m c) :=
  ((continuous_apply i).comp continuous_snd).continuousOn.mono (Set.subset_univ _)

lemma goodRegion_half {m : ℕ} (hm : 1 ≤ m) {x : (Fin m → ℂ) × (Fin m → ℂ)}
    (hx : x ∈ goodRegion m (-(1 / (6 * (m : ℝ))))) :
    ∀ i, -(1 / 2 : ℝ) < (x.1 i).re ∧ -(1 / 2 : ℝ) < (x.2 i).re := by
  intro i
  exact ⟨lt_trans (neg_half_lt_neg_inv_six hm) (hx.1 i),
    lt_trans (neg_half_lt_neg_inv_six hm) (hx.2 i)⟩

/-- `Re` of the updated vector stays above `c`. -/
lemma update_re_gt {z : Fin m → ℂ} {j : Fin m} {c : ℝ} (hz : ∀ i, c < (z i).re) {u : ℂ}
    (hu : c < u.re) : ∀ i, c < (Function.update z j u i).re := by
  intro i
  rw [Function.update_apply]
  split
  · exact hu
  · exact hz i

lemma update_re_ge {z : Fin m → ℂ} {j : Fin m} {c : ℝ} (hz : ∀ i, c ≤ (z i).re) {u : ℂ}
    (hu : c ≤ u.re) : ∀ i, c ≤ (Function.update z j u i).re := by
  intro i
  rw [Function.update_apply]
  split
  · exact hu
  · exact hz i

/-- `u ↦ Function.update z j u i` is holomorphic. -/
lemma differentiableOn_update (z : Fin m → ℂ) (j i : Fin m) :
    DifferentiableOn ℂ (fun u : ℂ => Function.update z j u i) Set.univ := by
  by_cases hij : i = j
  · rw [show (fun u : ℂ => Function.update z j u i) = fun u : ℂ => u by
        funext u; rw [hij, Function.update_apply, if_pos rfl]]
    exact differentiable_id.differentiableOn
  · rw [show (fun u : ℂ => Function.update z j u i) = fun _ : ℂ => z i by
        funext u; rw [Function.update_apply, if_neg hij]]
    exact (differentiable_const (z i)).differentiableOn

lemma E1p_sub_one_le_major' (H : LocHyp W Amax A b) (n : ℕ) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E1p W A b z z' n - 1‖ ≤ e1pMajor m n := by
  have hnn : (0 : ℝ) ≤ e1pMajor m n := by
    refine add_nonneg (by unfold cpowMajor; positivity) ?_
    by_cases h : n ≤ (6 * m) ^ 2 + 2
    · simp only [if_pos h]; positivity
    · simp [if_neg h]
  by_cases hn : n.Prime
  · by_cases hW : n ∣ W
    · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 hW), sub_self, norm_zero]
      exact hnn
    · exact E1p_sub_one_le_major H hn hW hz hz'
  · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1), sub_self, norm_zero]
    exact hnn

/-- `E1p` is continuous in the pair on the strip. -/
lemma continuousOn_E1p_pair (H : LocHyp W Amax A b) (n : ℕ) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E1p W A b x.1 x.2 n)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  by_cases hn : n.Prime
  · exact continuousOn_E1p_comp hn (fun i => continuousOn_fst_coord _ i)
      (fun i => continuousOn_snd_coord _ i) (fun x hx i => goodRegion_half H.hm hx i)
  · rw [show (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E1p W A b x.1 x.2 n) = fun _ => (1 : ℂ) by
      funext x; rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1)]]
    exact continuousOn_const

/-- `E2p` is continuous in the pair on the strip. -/
lemma continuousOn_E2p_pair (H : LocHyp W Amax A b) (n : ℕ) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E2p W x.1 x.2 n)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  by_cases hn : n.Prime
  · exact continuousOn_E2p_comp hn (fun i => continuousOn_fst_coord _ i)
      (fun i => continuousOn_snd_coord _ i) (fun x hx i => goodRegion_half H.hm hx i)
  · rw [show (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E2p W x.1 x.2 n) = fun _ => (1 : ℂ) by
      funext x; rw [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hn hc.1)]]
    exact continuousOn_const

/-- **`G₁` is continuous on the strip.** -/
lemma continuousOn_G1u (H : LocHyp W Amax A b) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G1u W A b x.1 x.2)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  have hfun : (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G1u W A b x.1 x.2)
      = fun x => ∏' n : ℕ, (1 + (E1p W A b x.1 x.2 n - 1)) := by
    funext x; rw [G1u]; exact tprod_congr (fun n => by ring)
  rw [hfun]
  refine Commons.Analysis.Complex.continuousOn_tprod_one_add_nat (isOpen_goodRegion m _)
    (summable_e1pMajor H.hm) ?_ ?_
  · exact Filter.Eventually.of_forall fun n x hx =>
      E1p_sub_one_le_major' H n (fun i => le_of_lt (hx.1 i)) (fun i => le_of_lt (hx.2 i))
  · intro n
    exact (continuousOn_E1p_pair H n).sub continuousOn_const

/-- **`G₁` is holomorphic along the coordinate line `u ↦ Function.update z j u`.-/
lemma differentiableAt_G1u_curve₁ (H : LocHyp W Amax A b) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G1u W A b (Function.update z j u) z') (z j) := by
  have hfun : (fun u : ℂ => G1u W A b (Function.update z j u) z')
      = fun u => ∏' n : ℕ, (1 + (E1p W A b (Function.update z j u) z' n - 1)) := by
    funext u; rw [G1u]; exact tprod_congr (fun n => by ring)
  rw [hfun]
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd := Commons.Analysis.Complex.differentiableOn_tprod_one_add_nat
    (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
    (f := fun n u => E1p W A b (Function.update z j u) z' n - 1)
    hs (summable_e1pMajor H.hm) ?_ ?_
  · exact hd.differentiableAt (hs.mem_nhds (hz j))
  · exact Filter.Eventually.of_forall fun n u hu =>
      E1p_sub_one_le_major' H n (fun i => le_of_lt (update_re_gt hz hu i))
        (fun i => le_of_lt (hz' i))
  · intro n
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z j i).mono (Set.subset_univ _)
      have h2 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z' i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => differentiableOn_const (c := z' i)
      refine (differentiableOn_E1p_comp
        (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn h1 h2 ?_).sub
        (differentiableOn_const (c := (1 : ℂ)))
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six H.hm) (update_re_gt hz hu i),
        lt_trans (neg_half_lt_neg_inv_six H.hm) (hz' i)⟩
    · rw [show (fun u : ℂ => E1p W A b (Function.update z j u) z' n - 1)
          = fun _ : ℂ => (0 : ℂ) by
        funext u; rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1), sub_self]]
      exact (differentiableOn_const (c := (0 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})

/-- **`G₁` is holomorphic along the coordinate line `u ↦ Function.update z' j u`.-/
lemma differentiableAt_G1u_curve₂ (H : LocHyp W Amax A b) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G1u W A b z (Function.update z' j u)) (z' j) := by
  have hfun : (fun u : ℂ => G1u W A b z (Function.update z' j u))
      = fun u => ∏' n : ℕ, (1 + (E1p W A b z (Function.update z' j u) n - 1)) := by
    funext u; rw [G1u]; exact tprod_congr (fun n => by ring)
  rw [hfun]
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd := Commons.Analysis.Complex.differentiableOn_tprod_one_add_nat
    (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
    (f := fun n u => E1p W A b z (Function.update z' j u) n - 1)
    hs (summable_e1pMajor H.hm) ?_ ?_
  · exact hd.differentiableAt (hs.mem_nhds (hz' j))
  · exact Filter.Eventually.of_forall fun n u hu =>
      E1p_sub_one_le_major' H n (fun i => le_of_lt (hz i))
        (fun i => le_of_lt (update_re_gt hz' hu i))
  · intro n
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} := fun i => differentiableOn_const (c := z i)
      have h2 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z' j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z' j i).mono (Set.subset_univ _)
      refine (differentiableOn_E1p_comp
        (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn h1 h2 ?_).sub
        (differentiableOn_const (c := (1 : ℂ)))
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six H.hm) (hz i),
        lt_trans (neg_half_lt_neg_inv_six H.hm) (update_re_gt hz' hu i)⟩
    · rw [show (fun u : ℂ => E1p W A b z (Function.update z' j u) n - 1)
          = fun _ : ℂ => (0 : ℂ) by
        funext u; rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1), sub_self]]
      exact (differentiableOn_const (c := (0 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})

/-! ## 8. The bound and holomorphy for `G₂`, and the bounds for `G₁` on the strip -/

/-- `-(1/2) ≤ Re w` for `Re w ≥ -1/(6m)`. -/
lemma le_neg_half_of {z : Fin m → ℂ} {j : Fin m} {m : ℕ} (hm : 1 ≤ m)
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z i).re) : -(1 / 2 : ℝ) ≤ (z j).re :=
  le_trans (le_of_lt (neg_half_lt_neg_inv_six hm)) (hz j)

/-- `-(1/2) ≤ Re (z_j + z'_j)` for `Re z, Re z' ≥ -1/(6m)`. -/
lemma le_neg_half_add {z z' : Fin m → ℂ} {j : Fin m} {m : ℕ} (hm : 1 ≤ m)
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z' i).re) :
    -(1 / 2 : ℝ) ≤ (z j + z' j).re := by
  rw [Complex.add_re]
  have h2 : -(2 * (1 / (6 * (m : ℝ)))) ≤ (z j).re + (z' j).re := by linarith [hz j, hz' j]
  have hpos : (0 : ℝ) < 6 * (m : ℝ) := by
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hB : -(1 / 2 : ℝ) ≤ -(2 * (1 / (6 * (m : ℝ)))) := by
    rw [neg_le_neg_iff]
    rw [show 2 * (1 / (6 * (m : ℝ))) = 2 / (6 * (m : ℝ)) by ring, div_le_iff₀ hpos]
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  linarith

/-- On the strip, `‖(1 - n^{-(1+w)})^{-1}‖ ≤ 4`. -/
lemma norm_inv_one_sub_cpow_le {n : ℕ} (hn : n.Prime) {w : ℂ}
    (hw : -(1 / 2 : ℝ) ≤ w.re) : ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + w)))⁻¹‖ ≤ 4 := by
  have hle := norm_cpow_le_three_quarters hn.two_le hw
  have hlow : (1 / 4 : ℝ) ≤ ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + w))‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((n : ℂ) ^ (-(1 + w)))
    rw [norm_one] at h
    linarith
  have hpos : (0 : ℝ) < ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + w))‖ :=
    lt_of_lt_of_le (by norm_num) hlow
  rw [norm_inv]
  calc (‖(1 : ℂ) - (n : ℂ) ^ (-(1 + w))‖)⁻¹ ≤ ((1 / 4 : ℝ))⁻¹ :=
        (inv_le_inv₀ hpos (by norm_num)).mpr hlow
    _ = 4 := by norm_num

/-- On the strip, `‖1 - n^{-(1+w)}‖ ≤ 2`. -/
lemma norm_one_sub_cpow_le {n : ℕ} (hn : n.Prime) {w : ℂ}
    (hw : -(1 / 2 : ℝ) ≤ w.re) : ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + w))‖ ≤ 2 := by
  have h := norm_sub_le (1 : ℂ) ((n : ℂ) ^ (-(1 + w)))
  rw [norm_one] at h
  have h2 := norm_cpow_le_three_quarters hn.two_le hw
  linarith

/-- `‖E2p‖ ≤ 32^m` on the strip. -/
lemma norm_E2p_le (H : LocHyp W Amax A b) (n : ℕ) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E2p W z z' n‖ ≤ (32 : ℝ) ^ m := by
  by_cases hc : n.Prime ∧ n ∣ W
  · rw [E2p, if_pos hc, norm_prod]
    have hperj : ∀ j : Fin m, ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖ ≤ 32 := by
      intro j
      rw [norm_mul, norm_mul]
      have hA := norm_inv_one_sub_cpow_le (n := n) hc.1 (w := z j) (le_neg_half_of H.hm hz)
      have hB := norm_inv_one_sub_cpow_le (n := n) hc.1 (w := z' j) (le_neg_half_of H.hm hz')
      have hC : ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))‖ ≤ 2 := by
        have h := norm_one_sub_cpow_le (n := n) hc.1 (w := z j + z' j)
          (le_neg_half_add H.hm hz hz')
        rwa [show (-(1 + (z j + z' j)) : ℂ) = -(1 + z j + z' j) by ring] at h
      calc ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹‖
            * ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹‖
            * ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))‖
          ≤ 4 * 4 * 2 :=
            mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by norm_num)) hC (norm_nonneg _)
              (by norm_num)
        _ ≤ 32 := by norm_num
    have h := Finset.prod_le_prod (s := Finset.univ)
      (f := fun j : Fin m => ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖)
      (g := fun _ : Fin m => (32 : ℝ)) (fun j _ => norm_nonneg _) (fun j _ => hperj j)
    simpa [Finset.prod_const, Finset.card_univ] using h
  · rw [E2p, if_neg hc, norm_one]
    exact one_le_pow₀ (by norm_num)

/-- **`G₂` is continuous on the strip.** -/
lemma continuousOn_G2u (H : LocHyp W Amax A b) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G2u W x.1 x.2)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  rw [show (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G2u W x.1 x.2)
      = fun x => ∏ n ∈ W.divisors, E2p W x.1 x.2 n by
    funext x; exact G2u_eq_prod H x.1 x.2]
  exact continuousOn_finsetProd' _ fun n _ => continuousOn_E2p_pair H n

/-- **`G₂` is holomorphic along the coordinate line `u ↦ Function.update z j u`.** -/
lemma differentiableAt_G2u_curve₁ (H : LocHyp W Amax A b) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G2u W (Function.update z j u) z') (z j) := by
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun u : ℂ => G2u W (Function.update z j u) z')
      {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} := by
    rw [show (fun u : ℂ => G2u W (Function.update z j u) z')
        = fun u => ∏ n ∈ W.divisors, E2p W (Function.update z j u) z' n by
      funext u; exact G2u_eq_prod H _ _]
    refine differentiableOn_finsetProd' _ fun n _ => ?_
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z j i).mono (Set.subset_univ _)
      have h2 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z' i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => differentiableOn_const (c := z' i)
      refine differentiableOn_E2p_comp (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn
        h1 h2 ?_
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six H.hm) (update_re_gt hz hu i),
        lt_trans (neg_half_lt_neg_inv_six H.hm) (hz' i)⟩
    · rw [show (fun u : ℂ => E2p W (Function.update z j u) z' n) = fun _ : ℂ => (1 : ℂ) by
        funext u; rw [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hn hc.1)]]
      exact (differentiableOn_const (c := (1 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
  exact hd.differentiableAt (hs.mem_nhds (hz j))

/-- **`G₂` is holomorphic along the coordinate line `u ↦ Function.update z' j u`.** -/
lemma differentiableAt_G2u_curve₂ (H : LocHyp W Amax A b) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G2u W z (Function.update z' j u)) (z' j) := by
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun u : ℂ => G2u W z (Function.update z' j u))
      {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} := by
    rw [show (fun u : ℂ => G2u W z (Function.update z' j u))
        = fun u => ∏ n ∈ W.divisors, E2p W z (Function.update z' j u) n by
      funext u; exact G2u_eq_prod H _ _]
    refine differentiableOn_finsetProd' _ fun n _ => ?_
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} := fun i => differentiableOn_const (c := z i)
      have h2 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z' j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z' j i).mono (Set.subset_univ _)
      refine differentiableOn_E2p_comp (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn
        h1 h2 ?_
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six H.hm) (hz i),
        lt_trans (neg_half_lt_neg_inv_six H.hm) (update_re_gt hz' hu i)⟩
    · rw [show (fun u : ℂ => E2p W z (Function.update z' j u) n) = fun _ : ℂ => (1 : ℂ) by
        funext u; rw [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hn hc.1)]]
      exact (differentiableOn_const (c := (1 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
  exact hd.differentiableAt (hs.mem_nhds (hz' j))

/-- **The bound `‖G₁‖ ≤ exp(∑ e1pMajor)` on the strip.** -/
lemma norm_G1u_le (H : LocHyp W Amax A b) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖G1u W A b z z'‖ ≤ Real.exp (∑' n : ℕ, e1pMajor m n) := by
  have hsum : Summable (fun n : ℕ => ‖E1p W A b z z' n - 1‖) :=
    E1p_summable H (by positivity) (sixth_small H.hm).1 (sixth_small H.hm).2 hz hz'
  rw [show G1u W A b z z' = ∏' n : ℕ, (1 + (E1p W A b z z' n - 1)) by
    rw [G1u]; exact tprod_congr (fun n => by ring)]
  refine le_trans (Commons.Analysis.Complex.norm_tprod_one_add_le_exp _ hsum) ?_
  refine Real.exp_le_exp.mpr ?_
  exact hsum.tsum_le_tsum (fun n => E1p_sub_one_le_major' H n hz hz') (summable_e1pMajor H.hm)

/-- **The bound `‖G₂‖ ≤ 32^(m · #divisors W)` on the strip.** -/
lemma norm_G2u_le (H : LocHyp W Amax A b) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖G2u W z z'‖ ≤ (32 : ℝ) ^ (m * W.divisors.card) := by
  rw [G2u_eq_prod H z z', norm_prod]
  have h := Finset.prod_le_prod (s := W.divisors) (f := fun n => ‖E2p W z z' n‖)
    (g := fun _ => (32 : ℝ) ^ m) (fun n _ => norm_nonneg _) (fun n _ => norm_E2p_le H n hz hz')
  calc ∏ n ∈ W.divisors, ‖E2p W z z' n‖ ≤ ∏ _n ∈ W.divisors, (32 : ℝ) ^ m := h
    _ = ((32 : ℝ) ^ m) ^ W.divisors.card := by rw [Finset.prod_const]
    _ = (32 : ℝ) ^ (m * W.divisors.card) := by rw [← pow_mul]

/-- The uniform bound `B` of Green–Tao Lemma 10.4 for `F = G₁G₂`. -/
noncomputable def stripBound (W m : ℕ) : ℝ :=
  Real.exp (∑' n : ℕ, e1pMajor m n) * (32 : ℝ) ^ (m * W.divisors.card)

/-! ## 9. Green–Tao Lemma 10.4 applied to `F = G₁G₂` -/

/-- **Green–Tao Lemma 10.4 for `F = G₁G₂`**: the `Γ₁`-contour integral of the `E^{(1)}E^{(2)}`-part
of the §10 Euler product (times the ζ-ratio and the kernel) equals
`G₁(0,0)G₂(0,0)(log R)^m` up to `O(C^m B(1 + (log R)^{m-1}) + C^m B e^{-δ√(log R)})`. -/
theorem zetaBound_G1G2 (H : LocHyp W Amax A b) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ R : ℝ, 3 ≤ R →
      ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
        (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
          (G1u W A b (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
            * G2u W (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
          * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
              / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
                  * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))))
          * (R : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
              + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
          * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta R (t j)) ^ 2
                * (Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)) ^ 2)⁻¹)
          * Complex.I ^ m * Complex.I ^ m)
        - (G1u W A b 0 0 * G2u (m := m) W 0 0) * (Real.log R) ^ m‖
      ≤ C ^ m * stripBound W m * (1 + (Real.log R) ^ (m - 1))
        + C ^ m * stripBound W m * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨δ, C, hδ, hC, Hmain⟩ := Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m H.hm
  refine ⟨δ, C, hδ, hC, fun R hR => ?_⟩
  refine Hmain R hR (fun z z' => G1u W A b z z' * G2u W z z') (stripBound W m) ?_ ?_ ?_ ?_ ?_
  · unfold stripBound; positivity
  · exact ((continuousOn_G1u H).mul (continuousOn_G2u H)).mono
      (fun x hx => ⟨fun i => (hx.1 i).1, fun i => (hx.2 i).1⟩)
  · intro j z z' hz hz'
    exact (differentiableAt_G1u_curve₁ H (fun i => (hz i).1) (fun i => (hz' i).1)).mul
      (differentiableAt_G2u_curve₁ H (fun i => (hz i).1) (fun i => (hz' i).1))
  · intro j z z' hz hz'
    exact (differentiableAt_G1u_curve₂ H (fun i => (hz i).1) (fun i => (hz' i).1)).mul
      (differentiableAt_G2u_curve₂ H (fun i => (hz i).1) (fun i => (hz' i).1))
  · intro z z' hz hz'
    rw [norm_mul]
    exact mul_le_mul (norm_G1u_le H (fun i => le_of_lt (hz i).1) (fun i => le_of_lt (hz' i).1))
      (norm_G2u_le H (fun i => le_of_lt (hz i).1) (fun i => le_of_lt (hz' i).1))
      (norm_nonneg _) (Real.exp_nonneg _)

end BoxAvg
end GYMaj
