import Mathlib
import Submission.ModelStarGate
import Submission.Commons.Topology.Simplex.brouwer_fixed_point_simplex

/-!
# ModelStarKKM -- the KKM lemma from Brouwer, and the GATE

This module
  * proves the KKM lemma `kkm` (for closed subsets of `ℝ^n` with the
    sub-simplex hypothesis) from Brouwer's fixed point theorem on the simplex
    (`Commons.Topology.Simplex.brouwer_fixed_point_simplex`);
  * derives `exists_tip_all_ge` (a gap vector all of whose tips are `≥ 4^(1/s)`)
    from it;
  * concludes **`sym_maximality`**: the full statement of
    `Submission.Step3.sym_maximality` (Dubinin's hedgehog inequality), hence the
    benchmark theorem.

The KKM-from-Brouwer argument: if `x₀` is a Brouwer fixed point of the
barycentric map `f x i := d(x, A i) / (Σ_k d(x, A k) + d(x, Δ))` (continuous
everywhere because the denominator vanishes only for `x ∈ Δ` inside all the
`A i`, which the sub-simplex hypothesis forbids), then the support
`I := {i : d(x₀, A i) > 0}` has `x₀ i = 0` off `I`, so `hsub I x₀` puts `x₀` in
some `A i` with `i ∈ I` — whence `d(x₀, A i) = 0`, a contradiction.
-/

noncomputable section

open scoped Real Topology BigOperators
open Set Filter Metric

namespace Submission.ModelStarKKM

open Submission.ModelStarExists

variable {s : ℕ}

/-- **The KKM lemma**, from Brouwer's fixed point theorem on the simplex. -/
theorem kkm : KKM := by
  intro n hn A hclosed hsub
  by_contra hcon
  push Not at hcon
  -- (0) each `A i` is nonempty (its own vertex lies in it, by `hsub {i}`)
  have hAne : ∀ i : Fin n, (A i).Nonempty := by
    intro i
    let v : Fin n → ℝ := fun j => if j = i then 1 else 0
    have hx0 : ∀ j, 0 ≤ v j := by
      intro j
      by_cases h : j = i <;> simp [v, h]
    have hx1 : (∑ j, v j) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj; simp [v, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hx2 : ∀ j, j ∉ ({i} : Finset (Fin n)) → v j = 0 := by
      intro j hj
      rw [Finset.mem_singleton] at hj
      simp [v, hj]
    obtain ⟨j, hj, hjm⟩ := hsub {i} v hx0 hx1 hx2
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨_, hjm⟩
  -- (1) the simplex
  set Δ : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1} with hΔ
  have hΔne : Δ.Nonempty :=
    ⟨fun _ => 1 / n, fun i => by positivity, by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp⟩
  have hΔclosed : IsClosed Δ := by
    have h1 : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
      rw [setOf_forall]
      exact isClosed_iInter fun i =>
        isClosed_le (continuous_const : Continuous fun _ : Fin n → ℝ => (0:ℝ))
          (continuous_apply i)
    have h2 : IsClosed {x : Fin n → ℝ | (∑ i, x i) = 1} :=
      isClosed_eq (continuous_finsetSum Finset.univ fun i _ => continuous_apply i)
        (continuous_const : Continuous fun _ : Fin n → ℝ => (1:ℝ))
    exact h1.inter h2
  -- (2) the weight sum and the barycentric map
  let S : (Fin n → ℝ) → ℝ := fun x => ∑ i, Metric.infDist x (A i)
  have hSnonneg : ∀ x, 0 ≤ S x := fun x =>
    Finset.sum_nonneg fun j _ => Metric.infDist_nonneg
  have hSpos : ∀ x ∈ Δ, 0 < S x := by
    intro x hx
    obtain ⟨i, hi⟩ := hcon x hx.1 hx.2
    refine Finset.sum_pos' (fun j _ => Metric.infDist_nonneg) ⟨i, Finset.mem_univ i, ?_⟩
    have hcl : x ∉ closure (A i) := by
      rwa [closure_eq_iff_isClosed.mpr (hclosed i)]
    exact lt_of_le_of_ne Metric.infDist_nonneg
      (Ne.symm (mt (Metric.mem_closure_iff_infDist_zero (hAne i)).mpr hcl))
  have hden : ∀ x : Fin n → ℝ, S x + Metric.infDist x Δ ≠ 0 := by
    intro x
    by_cases hx : x ∈ Δ
    · exact ne_of_gt (by linarith [Metric.infDist_nonneg (s := Δ) (x := x), hSpos x hx])
    · have hcl : x ∉ closure Δ := by rwa [closure_eq_iff_isClosed.mpr hΔclosed]
      have hpos : 0 < Metric.infDist x Δ := lt_of_le_of_ne Metric.infDist_nonneg
        (Ne.symm (mt (Metric.mem_closure_iff_infDist_zero hΔne).mpr hcl))
      exact ne_of_gt (by linarith [hSnonneg x])
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun x i =>
    Metric.infDist x (A i) / (S x + Metric.infDist x Δ)
  have hf : Continuous f := by
    refine continuous_pi fun i => Continuous.div ?_ ?_ hden
    · exact Metric.continuous_infDist_pt (A i)
    · exact (continuous_finsetSum Finset.univ fun j _ =>
        Metric.continuous_infDist_pt (A j)).add (Metric.continuous_infDist_pt Δ)
  have hmaps : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1 := by
    intro x hx0 hx1
    have hxΔ : x ∈ Δ := ⟨hx0, hx1⟩
    have h0 : Metric.infDist x Δ = 0 := Metric.infDist_zero_of_mem hxΔ
    constructor
    · intro i
      exact div_nonneg Metric.infDist_nonneg (add_nonneg (hSnonneg x) Metric.infDist_nonneg)
    · show (∑ i, Metric.infDist x (A i) / (S x + Metric.infDist x Δ)) = 1
      rw [← Finset.sum_div, h0, add_zero, div_self (ne_of_gt (hSpos x hxΔ))]
  -- (3) Brouwer
  obtain ⟨x₀, hx₀nn, hx₀sum, hfix⟩ :=
    Commons.Topology.Simplex.brouwer_fixed_point_simplex n hn f hf hmaps
  have h0 : Metric.infDist x₀ Δ = 0 := Metric.infDist_zero_of_mem ⟨hx₀nn, hx₀sum⟩
  have hS₀ : 0 < S x₀ := hSpos x₀ ⟨hx₀nn, hx₀sum⟩
  -- (4) the coordinates of the fixed point
  have hcoord : ∀ i : Fin n, x₀ i = Metric.infDist x₀ (A i) / S x₀ := by
    intro i
    have h := congrFun hfix i
    rw [show f x₀ i = Metric.infDist x₀ (A i) / (S x₀ + Metric.infDist x₀ Δ) from rfl,
      h0, add_zero] at h
    exact h.symm
  -- (5) the support
  set I : Finset (Fin n) := Finset.univ.filter (fun i => 0 < Metric.infDist x₀ (A i)) with hI
  have hIzero : ∀ i : Fin n, i ∉ I → x₀ i = 0 := by
    intro i hi
    rw [hI, Finset.mem_filter] at hi
    push Not at hi
    have hd : Metric.infDist x₀ (A i) = 0 := le_antisymm (hi (Finset.mem_univ i)) Metric.infDist_nonneg
    rw [hcoord i, hd, zero_div]
  obtain ⟨j, hjI, hjA⟩ := hsub I x₀ hx₀nn hx₀sum hIzero
  rw [hI, Finset.mem_filter] at hjI
  have : Metric.infDist x₀ (A j) = 0 := Metric.infDist_zero_of_mem hjA
  linarith [hjI.2]

/-- **The KKM output**: some gap vector has all tips `≥ 4^(1/s)`. -/
theorem exists_tip_all_ge (hs : 0 < s) (r : Fin s → ℝ) (hr : ∀ k, 0 < r k)
    (hsum : (∑ k, r k) = 1) :
    ∃ g : Fin s → ℝ, g ∈ Submission.ModelStarFamily.Simp ∧
      ∀ j, (4 : ℝ) ^ (1 / (s : ℝ)) ≤ Submission.ModelStarFamily.tip r g j :=
  exists_tip_all_ge_of_kkm kkm hs r hr hsum

/-- **The unit case of `Step3.sym_maximality`.** -/
theorem unit_case (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (hs : 1 ≤ u.card) :
    Filter.limsup (Submission.Step3Bridge.rootSeq u 1) Filter.atTop
      ≤ (4 : ℝ) ^ (-1 / (u.card : ℝ)) :=
  Submission.ModelStarGate.unit_case_of_kkm kkm u hu hs

/-- **THE GATE**: Dubinin's hedgehog inequality, i.e. the statement of
`Submission.Step3.sym_maximality`. -/
theorem sym_maximality (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1)
    (hs : 1 ≤ u.card) {L : ℝ} (hL : 0 ≤ L) :
    Filter.limsup (fun n : ℕ =>
        (Submission.FeketeLim.feketeNumber (Submission.Step3.dirStar u L) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop
      ≤ (L : ℝ) * (4 : ℝ) ^ (-1 / (u.card : ℝ)) :=
  Submission.Step3Bridge.sym_maximality_of_unit u hu hs hL (unit_case u hu hs)

end Submission.ModelStarKKM
