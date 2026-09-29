import Mathlib
import Submission.Work.Haupt.jtp_defs

/-!
# Holomorphy of the Jacobi triple product `jtpLHS x`

We show that for `‖x‖ < 1` the function
`z ↦ jtpLHS x z = ∏' n, (1 - x ^ (2(n+1))) * (1 + x ^ (2n+1) z) * (1 + x ^ (2n+1) / z)`
is complex differentiable at every `z ≠ 0`.

The product splits into the three convergent products
* `∏' n, (1 - x ^ (2(n+1)))` (constant),
* `∏' n, (1 + x ^ (2n+1) z)` (entire), and
* `∏' n, (1 + x ^ (2n+1) / z)` (holomorphic on `{0}ᶜ`),
each of which is a locally uniform limit of holomorphic partial products.
-/

namespace Work.Haupt

open Filter
open scoped BigOperators

noncomputable section

/-- If `∑ ‖c n‖ < ∞` then `z ↦ ∏' n, (1 + c n * z)` is entire. -/
lemma tprod_one_add_mul_differentiable (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) :
    Differentiable ℂ (fun z : ℂ => ∏' n : ℕ, (1 + c n * z)) := by
  rw [← differentiableOn_univ]
  have hloc : HasProdLocallyUniformlyOn (fun n z => 1 + c n * z)
      (fun z => ∏' n : ℕ, (1 + c n * z)) Set.univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro (K : Set ℂ) _ hcK
    obtain ⟨C, hC⟩ := hcK.exists_bound_of_continuousOn (f := fun z : ℂ => z) (by fun_prop)
    refine (hc.mul_left (max C 0)).hasProdUniformlyOn_nat_one_add hcK ?_ (fun n => ?_)
    · filter_upwards with n x hx
      rw [norm_mul, mul_comm ‖c n‖ ‖x‖]
      exact mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left C 0)) (norm_nonneg (c n))
    · fun_prop
  refine (hloc.tendstoLocallyUniformlyOn_finsetRange).differentiableOn ?_ isOpen_univ
  filter_upwards with N
  simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun _ _ => by fun_prop)

/-- If `∑ ‖c n‖ < ∞` then `z ↦ ∏' n, (1 + c n / z)` is holomorphic on `{0}ᶜ`. -/
lemma tprod_one_add_div_differentiableOn (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' n : ℕ, (1 + c n / z)) {0}ᶜ := by
  have hloc : HasProdLocallyUniformlyOn (fun n z => 1 + c n / z)
      (fun z => ∏' n : ℕ, (1 + c n / z)) {0}ᶜ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_compl_singleton
    intro (K : Set ℂ) hK hcK
    obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ ‖z‖ := by
      rcases K.eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, by simp [h]⟩
      · obtain ⟨z₀, hz₀K, hmin⟩ := hcK.exists_isMinOn h (f := fun z : ℂ => ‖z‖) (by fun_prop)
        refine ⟨‖z₀‖, ?_, fun z hz => hmin hz⟩
        have hz0 : z₀ ≠ 0 := by simpa using hK hz₀K
        exact norm_pos_iff.mpr hz0
    refine (hc.mul_left (1/δ)).hasProdUniformlyOn_nat_one_add hcK ?_ (fun n => ?_)
    · filter_upwards with n z hz
      rw [norm_div, div_eq_mul_inv]
      refine (div_le_div_of_nonneg_left (norm_nonneg _) hδpos (hδ z hz)).trans_eq ?_
      rw [div_eq_mul_inv, mul_comm, one_div]
    · refine continuousOn_const.div (by fun_prop) (fun z hz => ?_)
      simpa using hK hz
  refine (hloc.tendstoLocallyUniformlyOn_finsetRange).differentiableOn ?_ isOpen_compl_singleton
  filter_upwards with N
  refine DifferentiableOn.fun_finsetProd (f := fun i z => (1 + c i / z : ℂ))
    (u := Finset.range N) (fun i _ => ?_)
  refine DifferentiableOn.add (differentiableOn_const (c := (1:ℂ))) ?_
  refine DifferentiableOn.div (differentiableOn_const (c := c i)) (by fun_prop) (fun z hz => ?_)
  · simpa using hz

theorem jtpLHS_differentiableAt (x : ℂ) (hx1 : ‖x‖ < 1) :
    ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ (jtpLHS x) z := by
  intro z hz
  have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hgeom0 : Summable (fun n : ℕ => ‖x‖ ^ (2*n+1)) := by
    have h : Summable (fun n : ℕ => ‖x‖ * (‖x‖^2)^n) :=
      (summable_geometric_of_lt_one (sq_nonneg ‖x‖) hx2) |>.mul_left ‖x‖
    refine h.congr fun n => ?_
    rw [← pow_mul]; ring
  have hgeom : Summable (fun n : ℕ => ‖x ^ (2*n+1)‖) := by
    simpa only [norm_pow] using hgeom0
  have hA := tprod_one_add_mul_differentiable (fun n : ℕ => x ^ (2*n+1)) hgeom
  have hB := tprod_one_add_div_differentiableOn (fun n : ℕ => x ^ (2*n+1)) hgeom
  have hprod : DifferentiableOn ℂ
      (fun w : ℂ => (∏' n : ℕ, (1 - x ^ (2*(n+1)))) * (∏' n : ℕ, (1 + x^(2*n+1)*w))
        * (∏' n : ℕ, (1 + x^(2*n+1)/w))) {0}ᶜ := by
    have h2 : DifferentiableOn ℂ (fun w : ℂ => ∏' n : ℕ, (1 + x^(2*n+1)*w)) {0}ᶜ :=
      hA.differentiableOn.mono (Set.subset_univ _)
    exact ((differentiableOn_const (c := (∏' n : ℕ, (1 - x ^ (2*(n+1)))))).mul h2).mul hB
  have heq : Set.EqOn (jtpLHS x)
      (fun w : ℂ => (∏' n : ℕ, (1 - x ^ (2*(n+1)))) * (∏' n : ℕ, (1 + x^(2*n+1)*w))
        * (∏' n : ℕ, (1 + x^(2*n+1)/w))) {0}ᶜ := by
    intro w hw
    have hw0 : w ≠ 0 := by simpa using hw
    have h1 : Multipliable (fun n : ℕ => (1 - x^(2*(n+1)) : ℂ)) := by
      apply multipliable_one_add_of_summable (f := fun n ↦ - x ^ (2*(n+1)))
      have h2 : Summable (fun n : ℕ => (‖x‖^2)^(n+1)) :=
        (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (sq_nonneg ‖x‖) hx2)
      refine h2.congr fun n => ?_
      rw [norm_neg, norm_pow, ← pow_mul]
    have h2 : Multipliable (fun n : ℕ => (1 + x^(2*n+1)*w : ℂ)) := by
      apply multipliable_one_add_of_summable
      refine (hgeom.mul_left ‖w‖).congr fun n => ?_
      rw [norm_mul, mul_comm]
    have h3 : Multipliable (fun n : ℕ => (1 + x^(2*n+1)/w : ℂ)) := by
      apply multipliable_one_add_of_summable
      refine (hgeom.div_const ‖w‖).congr fun n => ?_
      rw [norm_div]
    calc jtpLHS x w
        = ∏' n : ℕ, ((1 - x ^ (2*(n+1))) * (1 + x^(2*n+1)*w) * (1 + x^(2*n+1)/w)) := rfl
      _ = ∏' n : ℕ, ((1 - x ^ (2*(n+1))) * ((1 + x^(2*n+1)*w) * (1 + x^(2*n+1)/w))) := by
          apply tprod_congr; intro n; ring
      _ = (∏' n : ℕ, (1 - x ^ (2*(n+1)))) * ∏' n : ℕ, ((1 + x^(2*n+1)*w) * (1 + x^(2*n+1)/w)) :=
          h1.tprod_mul (h2.mul h3)
      _ = (∏' n : ℕ, (1 - x ^ (2*(n+1)))) * ((∏' n : ℕ, (1 + x^(2*n+1)*w)) * (∏' n : ℕ, (1 + x^(2*n+1)/w))) := by
          rw [h2.tprod_mul h3]
      _ = (∏' n : ℕ, (1 - x ^ (2*(n+1)))) * (∏' n : ℕ, (1 + x^(2*n+1)*w)) * (∏' n : ℕ, (1 + x^(2*n+1)/w)) := by
          ring
  have hd : DifferentiableOn ℂ (jtpLHS x) {0}ᶜ := hprod.congr (fun w hw => heq hw)
  exact hd.differentiableAt (isOpen_compl_singleton.mem_nhds (by simpa using hz))

end

end Work.Haupt
