import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `jet_comp_l2`: the `L²` bound on the spatial jets of a composition `x ↦ Ψ (x, P x)`

This is the Leibniz/Faà di Bruno "tame" estimate used in the energy method for the DeTurck
nonlinearity: the `(s+1)`-st spatial jet of the composition `Ψ ∘ (·, P ·)` is controlled in `L²`
by the sup-norm bound `K` on the jets of `Ψ` up to order `s+1`, the sup-norm bound `A` on the
jets of `P` up to order `M ≥ (s+1)/2`, and the `L²` bound `Etop` on the jets of `P` up to order
`s+1`.

The proof has three ingredients.

* **Faà di Bruno.** `faaDiBruno_sum_le` bounds the norm of the `k`-th iterated derivative of a
  composition by a sum over the ordered finpartitions of `Fin k`, the term of a partition `c`
  being `‖D^{c.length} g (f x)‖ · ∏ i, ‖D^{c.partSize i} f x‖` (Mathlib's `iteratedFDeriv_comp`
  plus `OrderedFinpartition.norm_compAlongOrderedFinpartition_le`).
* **The pair map.** `norm_iteratedFDeriv_pair_le`: the `m`-th jet of `x ↦ (x, P x)`, `m ≥ 1`, is
  bounded by `max 1 ‖D^m P x‖`.
* **The Leibniz count.** With `∑ i, c.partSize i = s+1` and `M ≥ (s+1)/2`, *at most one* block of
  the partition exceeds `M` (`high_block_unique`); all other blocks contribute the sup bound
  `1 + A`, and the exceptional one contributes the single summand `‖D^m P x‖`, which is controlled
  by `L²` (`prod_one_add_le`).  Summing the `N = card (OrderedFinpartition (s+1))` partition terms
  (which all receive the same bound), Cauchy–Schwarz and the `L²` bounds for the jets of `P`
  finish the proof.
-/

noncomputable section

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

namespace JetComp

/-- A continuous real-valued function is integrable on the (bounded) unit cube. -/
lemma integrableOn_unitCube_of_continuous {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    Integrable g (volume.restrict (unitCube (ι := Fin n))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube (ι := Fin n) ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (hg.continuousOn.integrableOn_compact hC).mono_set hsub

/-- The volume of the unit cube is `1`. -/
lemma vol_unitCube (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) (unitCube (ι := Fin n)) = 1 := by
  rw [unitCube, Real.volume_pi_Ioc]
  simp

/-- The unit cube is measurable. -/
lemma measSet_unitCube (n : ℕ) : MeasurableSet (unitCube (ι := Fin n)) := by
  rw [unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

lemma integral_const_unitCube (n : ℕ) (c : ℝ) :
    ∫ _x in unitCube (ι := Fin n), c = c := by
  rw [MeasureTheory.setIntegral_const, Measure.real_def, vol_unitCube n, ENNReal.toReal_one,
    one_smul]

/-- **Faà di Bruno, norm form.**  The `k`-th iterated derivative of a composition is bounded by
the sum over the ordered finpartitions of `Fin k` of the obvious product of the norms of the
iterated derivatives of the two factors. -/
theorem faaDiBruno_sum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : F → G} {f : E → F} {x : E} (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (f x))
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖
      ≤ ∑ c : OrderedFinpartition k,
          ‖iteratedFDeriv ℝ c.length g (f x)‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) f x‖ := by
  rw [iteratedFDeriv_comp (n := (⊤ : ℕ∞)) hg hf
    (WithTop.coe_le_coe.mpr le_top : ((k : ℕ∞) : WithTop ℕ∞) ≤ _)]
  show ‖∑ c : OrderedFinpartition k,
      (ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun c _ => ?_
  exact OrderedFinpartition.norm_compAlongOrderedFinpartition_le c _ _

/-- **The Leibniz count.**  If a family of block sizes `m` of a partition of `s+1` is such that
`M ≥ (s+1)/2`, then at most one block size exceeds `M` (two of them would already add up to more
than `s+1`). -/
lemma high_block_unique {r s M : ℕ} (hM : (s + 1) / 2 ≤ M) (m : Fin r → ℕ)
    (hm : ∑ i, m i = s + 1) {i j : Fin r} (hi : M < m i) (hj : M < m j) : i = j := by
  by_contra h
  have hsub : ({i, j} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
  have h1 : m i + m j ≤ ∑ t, m t := by
    have h2 : (∑ t ∈ ({i,j} : Finset (Fin r)), m t) ≤ ∑ t, m t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => Nat.zero_le _)
    rw [Finset.sum_insert (by simpa using h), Finset.sum_singleton] at h2
    exact h2
  have h3 : 2 * (M + 1) ≤ m i + m j := by omega
  have h4 : (s + 1) ≤ 2 * M + 1 := by omega
  omega

/-- The iterated derivatives of order `≥ 1` of the identity are bounded by `1`. -/
lemma norm_iteratedFDeriv_id_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {m : ℕ} (hm : 1 ≤ m) : ‖iteratedFDeriv ℝ m (fun y : E => y) x‖ ≤ 1 := by
  obtain ⟨nn, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := fun y : E => y) (x := x)]
  rw [Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hfd : (fun y : E => fderiv ℝ (fun y : E => y) y)
      = fun _ : E => (ContinuousLinearMap.id ℝ E) := funext (fun y => fderiv_id)
  rw [hfd]
  rcases Nat.eq_zero_or_pos nn with hn | hn
  · subst hn
    rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : nn ≠ 0) (ContinuousLinearMap.id ℝ E)]
    simp

/-- The `m`-th iterated derivative, `m ≥ 1`, of the pair map `x ↦ (x, P x)` is bounded by
`max 1 ‖D^m P x‖`: the identity contributes `1` at order `1` and nothing at higher orders. -/
lemma norm_iteratedFDeriv_pair_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E → F) (x : E) (m : ℕ) (hm : 1 ≤ m) (hP : ContDiffAt ℝ (⊤ : ℕ∞) P x) :
    ‖iteratedFDeriv ℝ m (fun y : E => (y, P y)) x‖ ≤ max 1 ‖iteratedFDeriv ℝ m P x‖ := by
  have hprod : iteratedFDeriv ℝ m (fun y : E => (y, P y)) x
      = (iteratedFDeriv ℝ m (fun y : E => y) x).prod (iteratedFDeriv ℝ m P x) :=
    iteratedFDeriv_prodMk (f := fun y : E => y) (g := P) (contDiffAt_id (x := x)) hP
      (i := m) (WithTop.coe_le_coe.mpr le_top)
  rw [hprod, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (le_trans (norm_iteratedFDeriv_id_le x hm) (le_max_left (1 : ℝ) _))
    (le_max_right (1 : ℝ) _)

/-- The sum of the block sizes of an ordered finpartition of `Fin N` is `N`. -/
lemma sum_partSize {N : ℕ} (c : OrderedFinpartition N) : ∑ i, c.partSize i = N := by
  have h := Fintype.card_congr c.equivSigma
  rw [Fintype.card_sigma] at h
  simpa using h

/-- **The Leibniz count, quantitative form.**  A product `∏ i, (1 + ‖D^{m i} P x‖)` whose block
sizes add up to `s+1` and which has at most one exceptional index (`M < m i`) is bounded by
`(1+A)^{s+1} (1 + S x)`, where every non-exceptional factor is bounded by `1 + A` and `S` is the
sum of all the norms `‖D^k P x‖`, `k ≤ s+1`. -/
lemma prod_one_add_le {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : (Fin n → ℝ) → F) (A : ℝ) (hA : 0 ≤ A) (x : Fin n → ℝ)
    {r s M : ℕ}
    (hPsup : ∀ k ≤ M, ∀ y, ‖iteratedFDeriv ℝ k P y‖ ≤ A)
    (m : Fin r → ℕ) (hm : ∑ i, m i = s + 1) (hr : r ≤ s + 1)
    (hh : ∀ i j, M < m i → M < m j → i = j) :
    ∏ i, (1 + ‖iteratedFDeriv ℝ (m i) P x‖)
      ≤ (1 + A) ^ (s + 1) * (1 + ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖) := by
  classical
  set H : Finset (Fin r) := Finset.univ.filter (fun i => M < m i) with hH
  set L : Finset (Fin r) := Finset.univ.filter (fun i => ¬ M < m i) with hL
  have hcard : H.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hH] at hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hh i j hi hj
  have hsplit : (∏ i ∈ H, (1 + ‖iteratedFDeriv ℝ (m i) P x‖))
      * (∏ i ∈ L, (1 + ‖iteratedFDeriv ℝ (m i) P x‖))
      = ∏ i, (1 + ‖iteratedFDeriv ℝ (m i) P x‖) := by
    rw [hH, hL]
    exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin r => M < m i)
      (fun i => (1 + ‖iteratedFDeriv ℝ (m i) P x‖))
  have hlow : ∏ i ∈ L, (1 + ‖iteratedFDeriv ℝ (m i) P x‖) ≤ (1 + A) ^ (s + 1) := by
    have h1 : ∏ i ∈ L, (1 + ‖iteratedFDeriv ℝ (m i) P x‖) ≤ ∏ _i ∈ L, (1 + A) := by
      refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
      rw [hL] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      have := hPsup (m i) hi x
      linarith
    refine h1.trans ?_
    rw [Finset.prod_const]
    refine pow_le_pow_right₀ (by linarith) ?_
    have h2 : L.card ≤ (Finset.univ : Finset (Fin r)).card :=
      Finset.card_le_card (by rw [hL]; exact Finset.filter_subset _ _)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hhigh : ∏ i ∈ H, (1 + ‖iteratedFDeriv ℝ (m i) P x‖)
      ≤ 1 + ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖ := by
    rcases Nat.eq_zero_or_pos H.card with h0 | hpos
    · have hH0 : H = ∅ := Finset.card_eq_zero.mp h0
      rw [hH0, Finset.prod_empty]
      have hS0 : 0 ≤ ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖ :=
        Finset.sum_nonneg (fun k _ => norm_nonneg _)
      linarith
    · have h1 : H.card = 1 := le_antisymm hcard hpos
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
      rw [hi₀, Finset.prod_singleton]
      have hmi : m i₀ ≤ s + 1 := by
        rw [← hm]
        exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)
      have hmem : m i₀ ∈ Finset.range (s + 2) := Finset.mem_range.mpr (by omega)
      have hle : ‖iteratedFDeriv ℝ (m i₀) P x‖
          ≤ ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖ :=
        Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k P x‖)
          (fun k _ => norm_nonneg _) hmem
      linarith
  rw [← hsplit]
  have hH0 : (0 : ℝ) ≤ ∏ i ∈ H, (1 + ‖iteratedFDeriv ℝ (m i) P x‖) :=
    Finset.prod_nonneg (fun i _ => by positivity)
  have hL0 : (0 : ℝ) ≤ ∏ i ∈ L, (1 + ‖iteratedFDeriv ℝ (m i) P x‖) :=
    Finset.prod_nonneg (fun i _ => by positivity)
  have hB0 : (0 : ℝ) ≤ (1 + A) ^ (s + 1) := pow_nonneg (by linarith) _
  have hM0 : (0 : ℝ) ≤ 1 + ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖ := by
    have := Finset.sum_nonneg (s := Finset.range (s + 2))
      (f := fun k => ‖iteratedFDeriv ℝ k P x‖) (fun k _ => norm_nonneg _)
    linarith
  calc (∏ i ∈ H, (1 + ‖iteratedFDeriv ℝ (m i) P x‖))
        * (∏ i ∈ L, (1 + ‖iteratedFDeriv ℝ (m i) P x‖))
      ≤ (1 + ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖) * (1 + A) ^ (s + 1) :=
        mul_le_mul hhigh hlow hL0 hM0
    _ = (1 + A) ^ (s + 1) * (1 + ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖) := by
        ring

/-- **Cauchy–Schwarz for a finite sum, integrated over the cube.** -/
lemma integral_sq_sum_le {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → (Fin n → ℝ) → ℝ) (ha : ∀ i, Continuous (a i)) (_ha0 : ∀ i x, 0 ≤ a i x) :
    ∫ x in unitCube (ι := Fin n), (∑ i, a i x) ^ 2
      ≤ (Fintype.card ι : ℝ) * ∑ i, ∫ x in unitCube (ι := Fin n), a i x ^ 2 := by
  have hpt : ∀ x, (∑ i, a i x) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, a i x ^ 2 := by
    intro x
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => a i x)
    simpa using this
  have hc1 : Continuous (fun x : Fin n → ℝ => (∑ i, a i x) ^ 2) := by
    refine Continuous.pow ?_ 2
    exact continuous_finsetSum _ (fun i _ => ha i)
  have hc2 : Continuous (fun x : Fin n → ℝ => (Fintype.card ι : ℝ) * ∑ i, a i x ^ 2) := by
    refine Continuous.mul continuous_const ?_
    exact continuous_finsetSum _ (fun i _ => (ha i).pow 2)
  have hmono := MeasureTheory.setIntegral_mono_on
    (integrableOn_unitCube_of_continuous hc1) (integrableOn_unitCube_of_continuous hc2)
    (measSet_unitCube n) (fun x _ => hpt x)
  refine hmono.trans_eq ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_finset_sum (Finset.univ)
    (f := fun (i : ι) (x : Fin n → ℝ) => a i x ^ 2)
    (fun i _ => integrableOn_unitCube_of_continuous ((ha i).pow 2))


end JetComp

/-- The `L²` bound on the `(s+1)`-st partial derivatives of the composition
`x ↦ Ψ (x, P x)`: if the jets of `Ψ` are bounded by `K` up to order `s+1`, those of `P` by `A`
up to order `M ≥ (s+1)/2`, and the jets of `P` up to order `s+1` are bounded in `L²` by `Etop`,
then every `(s+1)`-st partial derivative of the composition is bounded in `L²` by
`C K² (1+A)^{2(s+2)} (1+Etop)`. -/

theorem jet_comp_l2 {n s M : ℕ} (hM : (s + 1) / 2 ≤ M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : (Fin n → ℝ) × F → ℂ) (P : (Fin n → ℝ) → F)
    (K A Etop : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hΨsm : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hPsm : ContDiff ℝ (⊤ : ℕ∞) P)
    (hΨ : ∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j Ψ (x, P x)‖ ≤ K)
    (hPsup : ∀ m ≤ M, ∀ x, ‖iteratedFDeriv ℝ m P x‖ ≤ A)
    (hPl2 : ∀ m ≤ s + 1, ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖iteratedFDeriv ℝ m P x‖ ^ 2 ≤ Etop) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Fin (s + 1) → Fin n),
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec (s + 1) l (fun x => Ψ (x, P x)) x‖ ^ 2
        ≤ C * K ^ 2 * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by
  classical
  set N : ℝ := (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) with hNdef
  set B : ℝ := N * K * (1 + A) ^ (s + 1) with hBdef
  set c : ℝ := ((s + 2 : ℕ) : ℝ) with hcdef
  set S : (Fin n → ℝ) → ℝ :=
    fun x => ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖ with hSdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc2 : (2 : ℝ) ≤ c := by
    rw [hcdef]
    exact_mod_cast (by omega : 2 ≤ s + 2)
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hS0 : ∀ x : Fin n → ℝ, 0 ≤ S x := by
    intro x
    rw [hSdef]
    exact Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hEtop0 : 0 ≤ Etop := by
    have h0 : 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖iteratedFDeriv ℝ 0 P x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have h1 := hPl2 0 (Nat.zero_le _)
    linarith
  have hfcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => Ψ (y, P y)) :=
    hΨsm.comp (contDiff_id.prodMk hPsm)
  refine ⟨2 * N ^ 2 * c ^ 2, by positivity, fun l => ?_⟩
  -- ### 1. the pointwise Faà di Bruno bound
  have hpt : ∀ x : Fin n → ℝ,
      ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ≤ B * (1 + S x) := by
    intro x
    have hfb := JetComp.faaDiBruno_sum_le (g := Ψ) (f := fun y : Fin n → ℝ => (y, P y))
      hΨsm.contDiffAt ((contDiffAt_id (x := x)).prodMk hPsm.contDiffAt) (s + 1)
    have hrw : (Ψ ∘ fun y : Fin n → ℝ => (y, P y)) = (fun y : Fin n → ℝ => Ψ (y, P y)) := rfl
    rw [hrw] at hfb
    refine hfb.trans ?_
    have hterm : ∀ d : OrderedFinpartition (s + 1),
        ‖iteratedFDeriv ℝ d.length Ψ (x, P x)‖ *
          ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
        ≤ K * ((1 + A) ^ (s + 1) * (1 + S x)) := by
      intro d
      have hKd : ‖iteratedFDeriv ℝ d.length Ψ (x, P x)‖ ≤ K := hΨ d.length d.length_le x
      have hPd : ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
          ≤ (1 + A) ^ (s + 1) * (1 + S x) := by
        have hstep : ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
            ≤ ∏ i, (1 + ‖iteratedFDeriv ℝ (d.partSize i) P x‖) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => by
            have h1 := JetComp.norm_iteratedFDeriv_pair_le P x (d.partSize i) (d.partSize_pos i)
              hPsm.contDiffAt
            have h2 : max (1 : ℝ) ‖iteratedFDeriv ℝ (d.partSize i) P x‖
                ≤ 1 + ‖iteratedFDeriv ℝ (d.partSize i) P x‖ :=
              max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left zero_le_one)
            linarith)
        refine hstep.trans ?_
        rw [hSdef]
        exact JetComp.prod_one_add_le P A hA x (fun k hk y => hPsup k hk y) (fun i => d.partSize i)
          (JetComp.sum_partSize d) d.length_le
          (fun i j hi hj => JetComp.high_block_unique hM _ (JetComp.sum_partSize d) hi hj)
      exact mul_le_mul hKd hPd (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hK
    calc ∑ d : OrderedFinpartition (s + 1),
          ‖iteratedFDeriv ℝ d.length Ψ (x, P x)‖ *
            ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
        ≤ ∑ _d : OrderedFinpartition (s + 1), K * ((1 + A) ^ (s + 1) * (1 + S x)) :=
          Finset.sum_le_sum fun d _ => hterm d
      _ = N * (K * ((1 + A) ^ (s + 1) * (1 + S x))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNdef]
      _ = B * (1 + S x) := by rw [hBdef]; ring
  -- ### 2. integration
  have hScont : Continuous S := by
    rw [hSdef]
    exact continuous_finsetSum _ (fun k _ =>
      (hPsm.continuous_iteratedFDeriv (m := k) (by simp)).norm)
  have hInt1 : Integrable (fun x : Fin n → ℝ =>
      ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2)
      (volume.restrict (unitCube (ι := Fin n))) :=
    JetComp.integrableOn_unitCube_of_continuous
      ((hfcd.continuous_iteratedFDeriv (m := s + 1) (by simp)).norm.pow 2)
  have hInt2 : Integrable (fun x : Fin n → ℝ => B ^ 2 * (1 + S x) ^ 2)
      (volume.restrict (unitCube (ι := Fin n))) :=
    JetComp.integrableOn_unitCube_of_continuous
      (continuous_const.mul ((continuous_const.add hScont).pow 2))
  have hmono : ∫ x in unitCube (ι := Fin n),
        ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2
      ≤ ∫ x in unitCube (ι := Fin n), B ^ 2 * (1 + S x) ^ 2 :=
    MeasureTheory.setIntegral_mono_on hInt1 hInt2 (JetComp.measSet_unitCube n) (fun x _ => by
      have h1 := hpt x
      have h2 : 0 ≤ B * (1 + S x) := mul_nonneg hB0 (by linarith [hS0 x])
      calc ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2
          = ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖
            * ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ := by ring
        _ ≤ (B * (1 + S x)) * (B * (1 + S x)) := mul_le_mul h1 h1 (norm_nonneg _) h2
        _ = B ^ 2 * (1 + S x) ^ 2 := by ring)
  -- the `L²` bound for `(1 + S)²`
  have hmonoS : ∫ x in unitCube (ι := Fin n), (1 + S x) ^ 2
      ≤ ∫ x in unitCube (ι := Fin n), 2 * (1 + S x ^ 2) :=
    MeasureTheory.setIntegral_mono_on
      (JetComp.integrableOn_unitCube_of_continuous ((continuous_const.add hScont).pow 2))
      (JetComp.integrableOn_unitCube_of_continuous
        (continuous_const.mul (continuous_const.add (hScont.pow 2))))
      (JetComp.measSet_unitCube n) (fun x _ => by
        have h := hS0 x
        nlinarith [sq_nonneg (S x - 1)])
  have hIntVal : ∫ x in unitCube (ι := Fin n), 2 * (1 + S x ^ 2)
      = 2 * (1 + ∫ x in unitCube (ι := Fin n), S x ^ 2) := by
    have hadd : ∫ x in unitCube (ι := Fin n), ((1 : ℝ) + S x ^ 2)
        = (∫ _x in unitCube (ι := Fin n), (1 : ℝ))
          + ∫ x in unitCube (ι := Fin n), S x ^ 2 :=
      MeasureTheory.integral_add (JetComp.integrableOn_unitCube_of_continuous continuous_const)
        (JetComp.integrableOn_unitCube_of_continuous (hScont.pow 2))
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [hadd, JetComp.integral_const_unitCube n 1]
  -- the `L²` bound for the jets of `P`
  have hSsum : ∀ x : Fin n → ℝ,
      S x = ∑ k : Fin (s + 2), ‖iteratedFDeriv ℝ (k : ℕ) P x‖ := by
    intro x
    simp only [hSdef]
    exact Finset.sum_range (n := s + 2) (f := fun k => ‖iteratedFDeriv ℝ k P x‖)
  have hcont_a : ∀ k : Fin (s + 2),
      Continuous (fun x : Fin n → ℝ => ‖iteratedFDeriv ℝ (k : ℕ) P x‖) :=
    fun k => (hPsm.continuous_iteratedFDeriv (m := (k : ℕ)) (by simp)).norm
  have hsq := JetComp.integral_sq_sum_le (n := n) (ι := Fin (s + 2))
    (a := fun k x => ‖iteratedFDeriv ℝ (k : ℕ) P x‖) hcont_a (fun k x => norm_nonneg _)
  have hsq' : ∫ x in unitCube (ι := Fin n), S x ^ 2
      ≤ ((s + 2 : ℕ) : ℝ) * ∑ k : Fin (s + 2),
          ∫ x in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ (k : ℕ) P x‖ ^ 2 := by
    simpa only [hSsum, Fintype.card_fin] using hsq
  have hsq2 : ∫ x in unitCube (ι := Fin n), S x ^ 2 ≤ c * (c * Etop) := by
    refine hsq'.trans ?_
    have hk : ∀ k : Fin (s + 2), (k : ℕ) ≤ s + 1 := by
      intro k
      have := k.isLt
      omega
    calc ((s + 2 : ℕ) : ℝ) * ∑ k : Fin (s + 2),
          ∫ x in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ (k : ℕ) P x‖ ^ 2
        ≤ ((s + 2 : ℕ) : ℝ) * ∑ _k : Fin (s + 2), Etop :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hPl2 (k : ℕ) (hk k))
            (by positivity)
      _ = ((s + 2 : ℕ) : ℝ) * (((s + 2 : ℕ) : ℝ) * Etop) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = c * (c * Etop) := by rw [hcdef]
  have hfinal : ∫ x in unitCube (ι := Fin n), (1 + S x) ^ 2 ≤ 2 * (1 + c ^ 2 * Etop) := by
    calc ∫ x in unitCube (ι := Fin n), (1 + S x) ^ 2
        ≤ ∫ x in unitCube (ι := Fin n), 2 * (1 + S x ^ 2) := hmonoS
      _ = 2 * (1 + ∫ x in unitCube (ι := Fin n), S x ^ 2) := hIntVal
      _ ≤ 2 * (1 + c * (c * Etop)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          linarith [hsq2]
      _ = 2 * (1 + c ^ 2 * Etop) := by ring
  have hmain : ∫ x in unitCube (ι := Fin n),
        ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2
      ≤ B ^ 2 * (2 * (1 + c ^ 2 * Etop)) := by
    calc ∫ x in unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2
        ≤ ∫ x in unitCube (ι := Fin n), B ^ 2 * (1 + S x) ^ 2 := hmono
      _ = B ^ 2 * ∫ x in unitCube (ι := Fin n), (1 + S x) ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ B ^ 2 * (2 * (1 + c ^ 2 * Etop)) := mul_le_mul_of_nonneg_left hfinal (sq_nonneg B)
  -- ### 3. arithmetic
  have harith : B ^ 2 * (2 * (1 + c ^ 2 * Etop))
      ≤ (2 * N ^ 2 * c ^ 2) * K ^ 2 * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by
    have hB2 : B ^ 2 = N ^ 2 * K ^ 2 * (1 + A) ^ (2 * (s + 1)) := by
      rw [hBdef, mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (s + 1) 2]
    rw [hB2]
    have hstep1 : 2 * (1 + c ^ 2 * Etop) ≤ c ^ 2 * (2 * (1 + Etop)) := by
      nlinarith [hc2, sq_nonneg c, hEtop0]
    have hAB : (1 + A) ^ (2 * (s + 1)) ≤ (1 + A) ^ (2 * (s + 2)) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hfac : (0 : ℝ) ≤ 2 * N ^ 2 * c ^ 2 * K ^ 2 * (1 + Etop) := by positivity
    calc N ^ 2 * K ^ 2 * (1 + A) ^ (2 * (s + 1)) * (2 * (1 + c ^ 2 * Etop))
        ≤ N ^ 2 * K ^ 2 * (1 + A) ^ (2 * (s + 1)) * (c ^ 2 * (2 * (1 + Etop))) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ = (2 * N ^ 2 * c ^ 2 * K ^ 2 * (1 + Etop)) * (1 + A) ^ (2 * (s + 1)) := by ring
      _ ≤ (2 * N ^ 2 * c ^ 2 * K ^ 2 * (1 + Etop)) * (1 + A) ^ (2 * (s + 2)) :=
          mul_le_mul_of_nonneg_left hAB hfac
      _ = (2 * N ^ 2 * c ^ 2) * K ^ 2 * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by ring
  -- ### 4. from the full jet to a fixed partial derivative
  have hpd_eq : ∀ x : Fin n → ℝ,
      pdVec (s + 1) l (fun y : Fin n → ℝ => Ψ (y, P y)) x
        = iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x
            (fun j => Pi.single (l j) (1 : ℝ)) :=
    fun x => Comp.pdVec_eq_iteratedFDeriv (s + 1) _ hfcd x l
  have hprod_tuple : ∏ j : Fin (s + 1),
      ‖(fun j' : Fin (s + 1) => (Pi.single (l j') (1 : ℝ) : Fin n → ℝ)) j‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
    rw [Pi.norm_single]
    norm_num
  have hpd_le : ∀ x : Fin n → ℝ,
      ‖pdVec (s + 1) l (fun y : Fin n → ℝ => Ψ (y, P y)) x‖
        ≤ ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ := by
    intro x
    rw [hpd_eq x]
    calc ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x
            (fun j => Pi.single (l j) (1 : ℝ))‖
        ≤ ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖
          * ∏ j, ‖(fun j' : Fin (s + 1) =>
              (Pi.single (l j') (1 : ℝ) : Fin n → ℝ)) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod_tuple (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ := mul_one _
  have hIntP : Integrable (fun x : Fin n → ℝ =>
      ‖pdVec (s + 1) l (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2)
      (volume.restrict (unitCube (ι := Fin n))) :=
    JetComp.integrableOn_unitCube_of_continuous
      ((continuous_pdVec (s + 1) l _ (hfcd.of_le (by simp))).norm.pow 2)
  calc ∫ x in unitCube (ι := Fin n),
        ‖pdVec (s + 1) l (fun x => Ψ (x, P x)) x‖ ^ 2
      ≤ ∫ x in unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ (s + 1) (fun y : Fin n → ℝ => Ψ (y, P y)) x‖ ^ 2 :=
        MeasureTheory.setIntegral_mono_on hIntP hInt1 (JetComp.measSet_unitCube n)
          (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hpd_le x) 2)
    _ ≤ B ^ 2 * (2 * (1 + c ^ 2 * Etop)) := hmain
    _ ≤ (2 * N ^ 2 * c ^ 2) * K ^ 2 * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := harith

end Work.Diff.STE.flat
