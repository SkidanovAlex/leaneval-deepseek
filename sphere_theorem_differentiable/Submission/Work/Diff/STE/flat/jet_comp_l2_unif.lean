import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.elliptic_lower
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform `L²` bound for the iterated derivatives of `x ↦ Ψ (x, P x)`

This file proves `Work.Diff.STE.flat.jet_comp_l2_unif`: the constant in the flat composition
estimate of the DeTurck operator is **uniform** in the data (it depends only on `n`, `s` and `M`).

The mathematical content is the multivariate Faà di Bruno formula together with the observation
that, because the block sizes `p i` of an ordered partition of `{0, …, s}` satisfy
`∑ i, p i = s + 1`, **at most one** block can have size `> M` as soon as `2 * M ≥ s`
(which is exactly `(s + 1) / 2 ≤ M`).  Hence in each term of the chain rule at most one factor is
a derivative of `P` of order exceeding `M`; all the other factors are controlled by the sup bound
`A`, while the exceptional one is controlled in `L²` by `Etop`.

Structure of the proof:

* `iteratedFDeriv_comp_sum_gen` — Faà di Bruno as a sum over ordered partitions;
* `norm_iteratedFDeriv_pairMap_apply_le` — `‖D^p (fun y => (y, P y)) x u‖ ≤ max 1 ‖D^p P x‖` for
  a tuple `u` of unit vectors (the identity coordinate contributes at most `1`);
* `norm_chainTerm_le` — the per-partition term bound;
* `integral_prod_block_bound` — the `L²` bookkeeping using the "at most one big block" fact;
* `jet_comp_l2_unif` — assembly with Cauchy–Schwarz over the finitely many partitions.
-/

noncomputable section

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

/-! ## 1. Faà di Bruno as a sum over ordered partitions -/

/-- **Faà di Bruno formula** for the iterated Fréchet derivative of a composition of a scalar
function `Φ : G → H` with a curve `V : E → G`, evaluated at an `s`-tuple of vectors: the sum over
the ordered set partitions of `Fin s`. -/
theorem iteratedFDeriv_comp_sum_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s : ℕ) (Φ : G → H) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (V : E → G) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (x : E) (v : Fin s → E) :
    iteratedFDeriv ℝ s (fun y => Φ (V y)) x v
      = ∑ c : OrderedFinpartition s,
          (iteratedFDeriv ℝ c.length Φ (V x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) V x (v ∘ c.emb i)) := by
  have h1 : iteratedFDeriv ℝ s (fun y => Φ (V y)) x
      = (ftaylorSeries ℝ Φ (V x)).taylorComp (ftaylorSeries ℝ V x) s :=
    iteratedFDeriv_comp (g := Φ) (f := V) (hΦ.contDiffAt) (hV.contDiffAt)
      (WithTop.coe_le_coe.mpr le_top : ((s : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  rw [h1]
  simp only [FormalMultilinearSeries.taylorComp, ftaylorSeries, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply]

/-! ## 2. Auxiliary combinatorial and analytic facts -/

/-- The block sizes of an ordered partition of `Fin N` sum to `N`. -/
lemma sum_partSize_flat {N : ℕ} (c : OrderedFinpartition N) : ∑ m, c.partSize m = N := by
  have h : ∑ m, c.partSize m
      = Fintype.card ((m : Fin c.length) × Fin (c.partSize m)) := by
    rw [Fintype.card_sigma]
    simp
  rw [h, Fintype.card_congr c.equivSigma, Fintype.card_fin]

/-- The iterated derivatives of the identity: for `p ≥ 1` the norm is at most `1`
(the first derivative is the identity, all the higher ones vanish). -/
lemma norm_iteratedFDeriv_self_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {p : ℕ} (hp : 1 ≤ p) :
    ‖iteratedFDeriv ℝ p (fun y : E => y) x‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := fun y : E => y) (x := x)]
  rw [Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hfd : (fun y : E => fderiv ℝ (fun y : E => y) y) =
      fun _ : E => (ContinuousLinearMap.id ℝ E) := funext fun y => fderiv_id
  rw [hfd]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : k ≠ 0) (ContinuousLinearMap.id ℝ E)]
    simp

/-- **The iterated derivatives of the pair map.**  For a tuple `u` of unit vectors,
`‖D^p (fun y => (y, P y)) x u‖ ≤ max 1 ‖D^p P x‖`: the identity coordinate contributes at most
`1`, the `P`-coordinate at most `‖D^p P x‖`. -/
lemma norm_iteratedFDeriv_pairMap_apply_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E → F) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (x : E) {p : ℕ} (hp : 1 ≤ p)
    (u : Fin p → E) (hu : ∀ j, ‖u j‖ = 1) :
    ‖iteratedFDeriv ℝ p (fun y : E => (y, P y)) x u‖ ≤ max 1 ‖iteratedFDeriv ℝ p P x‖ := by
  have hprod : iteratedFDeriv ℝ p (fun y : E => (y, P y)) x
      = (iteratedFDeriv ℝ p (fun y : E => y) x).prod (iteratedFDeriv ℝ p P x) :=
    iteratedFDeriv_prodMk (contDiffAt_id (x := x)) hP.contDiffAt
      (WithTop.coe_le_coe.mpr le_top)
  rw [hprod, ContinuousMultilinearMap.prod_apply, Prod.norm_mk]
  have hprod1 : (∏ j : Fin p, ‖u j‖) = 1 := Finset.prod_eq_one fun j _ => hu j
  refine max_le ?_ ?_
  · refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    rw [hprod1, mul_one]
    exact (norm_iteratedFDeriv_self_le x hp).trans (le_max_left _ _)
  · refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    rw [hprod1, mul_one]
    exact le_max_right _ _

/-- **The per-partition term bound.**  Each term of the Faà di Bruno expansion of
`D^{s+1} (x ↦ Ψ (x, P x))` is bounded by `K` times the product of the per-block bounds
`max 1 A` (for small blocks, controlled by the sup bound `A`) and
`max 1 ‖D^{p} P x‖` (for a block of size `p > M`, controlled later in `L²`). -/
theorem norm_chainTerm_le {n s M : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : (Fin n → ℝ) × F → ℂ) (P : (Fin n → ℝ) → F) (K A : ℝ)
    (hPsm : ContDiff ℝ (⊤ : ℕ∞) P)
    (hΨ : ∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j Ψ (x, P x)‖ ≤ K)
    (hPsup : ∀ m ≤ M, ∀ x, ‖iteratedFDeriv ℝ m P x‖ ≤ A)
    (l : Fin (s + 1) → Fin n) (c : OrderedFinpartition (s + 1)) (x : Fin n → ℝ) :
    ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
          (fun j => (Pi.single (l (c.emb i j)) (1 : ℝ) : Fin n → ℝ)))‖
      ≤ K * ∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hΨ 0 (Nat.zero_le _) x)
  have hblk : ∀ i : Fin c.length,
      ‖iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
          (fun j => (Pi.single (l (c.emb i j)) (1 : ℝ) : Fin n → ℝ))‖
        ≤ (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) := by
    intro i
    have hp : 1 ≤ c.partSize i := c.partSize_pos i
    have hnorm : ∀ j : Fin (c.partSize i),
        ‖(fun j' => (Pi.single (l (c.emb i j')) (1 : ℝ) : Fin n → ℝ)) j‖ = 1 := fun j => by
      rw [Pi.norm_single, norm_one]
    have h := norm_iteratedFDeriv_pairMap_apply_le P hPsm x (p := c.partSize i) hp
      (fun j => (Pi.single (l (c.emb i j)) (1 : ℝ) : Fin n → ℝ)) hnorm
    by_cases hle : c.partSize i ≤ M
    · rw [if_pos hle]
      exact h.trans (max_le_max le_rfl (hPsup _ hle x))
    · rw [if_neg hle]
      exact h
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  refine mul_le_mul (hΨ c.length c.length_le x)
    (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hblk i)) ?_ hK0
  exact Finset.prod_nonneg fun i _ => by positivity

/-! ## 3. The `L²` bookkeeping -/

/-- The integral of `1` over the unit cube. -/
lemma integral_one_unitCube (n : ℕ) :
    ∫ x in unitCube (ι := Fin n), (1 : ℝ) = 1 := by
  have hvol : (volume.restrict (unitCube (ι := Fin n)) : Measure (Fin n → ℝ)).real Set.univ = 1 := by
    show ((volume.restrict (unitCube (ι := Fin n)) : Measure (Fin n → ℝ)) Set.univ).toReal = 1
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      BesselCont.vol_unitCube]
    norm_num
  rw [MeasureTheory.integral_const, hvol, one_smul]

/-- Continuity of the per-block bound `max 1 ‖D^p P‖` for a smooth `P`. -/
lemma continuous_max_one_norm_iteratedFDeriv {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P : (Fin n → ℝ) → F) (hPsm : ContDiff ℝ (⊤ : ℕ∞) P) (p : ℕ) :
    Continuous fun x : Fin n → ℝ => max 1 ‖iteratedFDeriv ℝ p P x‖ :=
  continuous_const.max (hPsm.continuous_iteratedFDeriv (m := p) (by simp)).norm

/-- **The `L²` bookkeeping.**  At most one block of an ordered partition of `Fin (s+1)` can have
size `> M` when `(s + 1) / 2 ≤ M`; the corresponding factor is controlled in `L²` by `Etop`, all
the other factors by `max 1 A`. -/
theorem integral_prod_block_bound {n s M : ℕ} (hM : (s + 1) / 2 ≤ M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : (Fin n → ℝ) → F) (hPsm : ContDiff ℝ (⊤ : ℕ∞) P)
    (A Etop : ℝ) (hEtop : 0 ≤ Etop)
    (hPl2 : ∀ m ≤ s + 1, ∫ x in unitCube (ι := Fin n),
        ‖iteratedFDeriv ℝ m P x‖ ^ 2 ≤ Etop)
    (c : OrderedFinpartition (s + 1)) :
    ∫ x in unitCube (ι := Fin n),
        (∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2
      ≤ (max 1 A) ^ (2 * (s + 1)) * (1 + Etop) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (unitCube (ι := Fin n))) :=
    BesselCont.isFiniteMeasure_restrict_unitCube
  set B : ℝ := max 1 A with hBdef
  have hB1 : 1 ≤ B := le_max_left 1 A
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  set J : Finset (Fin c.length) := Finset.univ.filter fun i => M < c.partSize i with hJdef
  have hJmem : ∀ i : Fin c.length, i ∈ J ↔ M < c.partSize i := by
    intro i; simp [hJdef]
  -- at most one block can be larger than `M`
  have hJcard : J.card ≤ 1 := by
    by_contra hlt
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
    have hi' : M < c.partSize i := (hJmem i).mp hi
    have hj' : M < c.partSize j := (hJmem j).mp hj
    have hsub : ({i, j} : Finset (Fin c.length)) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => Nat.zero_le (c.partSize m))
    rw [Finset.sum_pair hij] at hle
    have hsum : ∑ m, c.partSize m = s + 1 := sum_partSize_flat c
    have hle' : c.partSize i + c.partSize j ≤ s + 1 := by
      calc c.partSize i + c.partSize j ≤ ∑ m, c.partSize m := hle
        _ = s + 1 := hsum
    have hs : s ≤ 2 * M := by omega
    omega
  -- the pointwise factor, rewritten in terms of `J`
  have hfac : ∀ (i : Fin c.length) (x : Fin n → ℝ),
      (if c.partSize i ≤ M then max 1 A
        else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)
      = if i ∈ J then max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖ else B := by
    intro i x
    by_cases hi : i ∈ J
    · have hMi : M < c.partSize i := (hJmem i).mp hi
      rw [if_neg (by omega : ¬ c.partSize i ≤ M), if_pos hi]
    · have hMi : c.partSize i ≤ M := by
        have := (hJmem i).not.mp hi; omega
      rw [if_pos hMi, if_neg hi, hBdef]
  -- the exact factorisation of the square of the product
  have hsq : ∀ x : Fin n → ℝ,
      (∏ i : Fin c.length,
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2
      = (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2)
        * (B ^ 2) ^ (Jᶜ).card := by
    intro x
    rw [← Finset.prod_pow]
    rw [← Finset.prod_mul_prod_compl J (fun i => (if c.partSize i ≤ M then max 1 A
      else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2)]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by rw [hfac i x, if_pos hi]
    · exact (Finset.prod_congr rfl fun i hi => by rw [hfac i x, if_neg (by simpa using hi)]).trans
        (Finset.prod_const (s := Jᶜ) (B ^ 2))
  -- the pointwise bound, with the exceptional factor isolated
  have hpt : ∀ x : Fin n → ℝ,
      (∏ i : Fin c.length,
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2
      ≤ B ^ (2 * (s + 1))
        * (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) := by
    intro x
    rw [hsq x]
    have hcard : (Jᶜ).card ≤ s + 1 := by
      calc (Jᶜ).card ≤ (Finset.univ : Finset (Fin c.length)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = c.length := by simp
        _ ≤ s + 1 := c.length_le
    have hpow : B ^ (2 * (Jᶜ).card) ≤ B ^ (2 * (s + 1)) :=
      pow_le_pow_right₀ hB1 (by omega)
    have hprod0 : 0 ≤ ∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2 :=
      Finset.prod_nonneg fun i _ => by positivity
    calc (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) * (B ^ 2) ^ (Jᶜ).card
        = (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2)
          * B ^ (2 * (Jᶜ).card) := by rw [pow_mul]
      _ ≤ (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2)
          * B ^ (2 * (s + 1)) := mul_le_mul_of_nonneg_left hpow hprod0
      _ = B ^ (2 * (s + 1))
          * (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) := mul_comm _ _
  -- the integral of the exceptional product
  have hJint : ∫ x in unitCube (ι := Fin n),
      (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) ≤ 1 + Etop := by
    rcases Nat.eq_zero_or_pos J.card with h0 | hpos
    · have hJemp : J = ∅ := Finset.card_eq_zero.mp h0
      have hcong : (fun x : Fin n → ℝ =>
            ∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2)
          = fun _ : Fin n → ℝ => (1 : ℝ) := by
        funext x
        rw [hJemp, Finset.prod_empty]
      rw [hcong, integral_one_unitCube]
      linarith
    · have hJ1 : J.card = 1 := by omega
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hJ1
      have hcong : (fun x : Fin n → ℝ =>
            ∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2)
          = fun x : Fin n → ℝ =>
            (max 1 ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖) ^ 2 := by
        funext x
        rw [hi₀, Finset.prod_singleton]
      rw [hcong]
      have hcontL : Continuous fun x : Fin n → ℝ =>
          (max 1 ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖) ^ 2 :=
        (continuous_max_one_norm_iteratedFDeriv P hPsm (c.partSize i₀)).pow 2
      have hcontR : Continuous fun x : Fin n → ℝ =>
          (1 : ℝ) + ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ ^ 2 :=
        continuous_const.add
          ((hPsm.continuous_iteratedFDeriv (m := c.partSize i₀) (by simp)).norm.pow 2)
      have hptone : ∀ x : Fin n → ℝ,
          (max 1 ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖) ^ 2 ≤
            (1 : ℝ) + ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ ^ 2 := by
        intro x
        rcases le_total 1 ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ with h | h
        · rw [max_eq_right h]; nlinarith [sq_nonneg ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖]
        · rw [max_eq_left h]; nlinarith [sq_nonneg ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖]
      have hint2 : Integrable (fun x : Fin n → ℝ =>
          ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ ^ 2) (volume.restrict (unitCube (ι := Fin n))) :=
        el_integrableOn_unitCube_of_continuous_real
          ((hPsm.continuous_iteratedFDeriv (m := c.partSize i₀) (by simp)).norm.pow 2)
      calc ∫ x in unitCube (ι := Fin n),
            (max 1 ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖) ^ 2
          ≤ ∫ x in unitCube (ι := Fin n),
              ((1 : ℝ) + ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ ^ 2) :=
            integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
              (el_integrableOn_unitCube_of_continuous_real hcontR)
              (Filter.Eventually.of_forall hptone)
        _ = (∫ x in unitCube (ι := Fin n), (1 : ℝ))
              + ∫ x in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ ^ 2 :=
            integral_add (integrable_const (1 : ℝ)) hint2
        _ = 1 + ∫ x in unitCube (ι := Fin n),
              ‖iteratedFDeriv ℝ (c.partSize i₀) P x‖ ^ 2 := by rw [integral_one_unitCube]
        _ ≤ 1 + Etop := by
            have := hPl2 (c.partSize i₀) (c.partSize_le i₀)
            linarith
  -- assembly
  have hcontL : Continuous fun x : Fin n → ℝ =>
      (∏ i : Fin c.length,
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
    have hf : ∀ i : Fin c.length, Continuous fun x : Fin n → ℝ =>
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) := by
      intro i
      by_cases h : c.partSize i ≤ M
      · exact (continuous_const : Continuous fun _ : Fin n → ℝ => max 1 A).congr
          (fun x => by rw [if_pos h])
      · exact (continuous_max_one_norm_iteratedFDeriv P hPsm (c.partSize i)).congr
          (fun x => by rw [if_neg h])
    exact (continuous_finsetProd Finset.univ fun i _ => hf i).pow 2
  have hcontR : Continuous fun x : Fin n → ℝ => B ^ (2 * (s + 1))
      * (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) :=
    continuous_const.mul (continuous_finsetProd J fun i _ =>
      (continuous_max_one_norm_iteratedFDeriv P hPsm (c.partSize i)).pow 2)
  calc ∫ x in unitCube (ι := Fin n),
        (∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2
      ≤ ∫ x in unitCube (ι := Fin n), B ^ (2 * (s + 1))
          * (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) :=
        integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
          (el_integrableOn_unitCube_of_continuous_real hcontR)
          (Filter.Eventually.of_forall hpt)
    _ = B ^ (2 * (s + 1)) * ∫ x in unitCube (ι := Fin n),
          (∏ i ∈ J, (max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) ^ 2) :=
        integral_const_mul _ _
    _ ≤ B ^ (2 * (s + 1)) * (1 + Etop) := mul_le_mul_of_nonneg_left hJint (by positivity)
    _ = (max 1 A) ^ (2 * (s + 1)) * (1 + Etop) := by rw [hBdef]

/-! ## 4. The uniform composition estimate -/

theorem jet_comp_l2_unif {n s M : ℕ} (hM : (s + 1) / 2 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (Ψ : (Fin n → ℝ) × F → ℂ) (P : (Fin n → ℝ) → F) (K A Etop : ℝ)
      (hA : 0 ≤ A) (hK : 0 ≤ K)
      (hΨsm : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hPsm : ContDiff ℝ (⊤ : ℕ∞) P)
      (hΨ : ∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j Ψ (x, P x)‖ ≤ K)
      (hPsup : ∀ m ≤ M, ∀ x, ‖iteratedFDeriv ℝ m P x‖ ≤ A)
      (hPl2 : ∀ m ≤ s + 1, ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖iteratedFDeriv ℝ m P x‖ ^ 2 ≤ Etop)
      (l : Fin (s + 1) → Fin n),
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec (s + 1) l (fun x => Ψ (x, P x)) x‖ ^ 2
        ≤ C * K ^ 2 * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by
  classical
  refine ⟨(Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2, by positivity, ?_⟩
  intro F _ _ Ψ P K A Etop hA hK hΨsm hPsm hΨ hPsup hPl2 l
  set N : ℝ := (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  -- `Etop ≥ 0`
  have hEtop : 0 ≤ Etop := by
    have h := integral_nonneg
      (μ := volume.restrict (unitCube (ι := Fin n)))
      (f := fun x : Fin n → ℝ => ‖iteratedFDeriv ℝ 0 P x‖ ^ 2) (fun x => by positivity)
    exact h.trans (hPl2 0 (Nat.zero_le _))
  -- smoothness of the composite
  have hcomp_sm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Ψ (x, P x)) :=
    hΨsm.comp (contDiff_id.prodMk hPsm)
  -- `pdVec` versus `iteratedFDeriv`
  have hpd : ∀ x : Fin n → ℝ,
      pdVec (s + 1) l (fun x => Ψ (x, P x)) x
        = iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
            (fun j => Pi.single (l j) (1 : ℝ)) :=
    fun x => Comp.pdVec_eq_iteratedFDeriv (s + 1) _ hcomp_sm x l
  -- Faà di Bruno
  have hfab : ∀ x : Fin n → ℝ,
      iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
          (fun j => Pi.single (l j) (1 : ℝ))
        = ∑ c : OrderedFinpartition (s + 1),
            (iteratedFDeriv ℝ c.length Ψ (x, P x))
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
                ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i)) := by
    intro x
    have h := iteratedFDeriv_comp_sum_gen (s + 1) Ψ hΨsm (fun y : Fin n → ℝ => (y, P y))
      (contDiff_id.prodMk hPsm) x (fun j => Pi.single (l j) (1 : ℝ))
    simpa using h
  -- the pointwise Cauchy–Schwarz + term bound
  have hpt : ∀ x : Fin n → ℝ,
      ‖iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
          (fun j => Pi.single (l j) (1 : ℝ))‖ ^ 2
        ≤ N * ∑ c : OrderedFinpartition (s + 1),
            K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
    intro x
    rw [hfab x]
    have h1 : ‖∑ c : OrderedFinpartition (s + 1),
          (iteratedFDeriv ℝ c.length Ψ (x, P x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
              ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖ ^ 2
        ≤ N * ∑ c : OrderedFinpartition (s + 1),
            ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
                ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖ ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun c : OrderedFinpartition (s + 1) =>
          ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
              ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖)
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      simpa [hNdef, Finset.card_univ] using h
    refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hN0)
    calc ‖(iteratedFDeriv ℝ c.length Ψ (x, P x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y : Fin n → ℝ => (y, P y)) x
              ((fun j => Pi.single (l j) (1 : ℝ)) ∘ c.emb i))‖ ^ 2
        ≤ (K * ∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (norm_chainTerm_le Ψ P K A hPsm hΨ hPsup l c x) 2
      _ = K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by ring
  -- continuity / integrability
  have hcontL : Continuous fun x : Fin n → ℝ =>
      ‖iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
        (fun j => Pi.single (l j) (1 : ℝ))‖ ^ 2 := by
    have h1 : Continuous (iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x))) :=
      hcomp_sm.continuous_iteratedFDeriv (m := s + 1) (by simp)
    fun_prop
  have hfacs : ∀ c : OrderedFinpartition (s + 1), Continuous fun x : Fin n → ℝ =>
      K ^ 2 * (∏ i : Fin c.length,
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
    intro c
    have hf : ∀ i : Fin c.length, Continuous fun x : Fin n → ℝ =>
        (if c.partSize i ≤ M then max 1 A
         else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖) := by
      intro i
      by_cases h : c.partSize i ≤ M
      · exact (continuous_const : Continuous fun _ : Fin n → ℝ => max 1 A).congr
          (fun x => by rw [if_pos h])
      · exact (continuous_max_one_norm_iteratedFDeriv P hPsm (c.partSize i)).congr
          (fun x => by rw [if_neg h])
    exact continuous_const.mul ((continuous_finsetProd Finset.univ fun i _ => hf i).pow 2)
  have hcontR : Continuous fun x : Fin n → ℝ =>
      N * ∑ c : OrderedFinpartition (s + 1),
        K ^ 2 * (∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ fun c _ => hfacs c)
  -- the final estimate
  have hper : ∀ c : OrderedFinpartition (s + 1),
      ∫ x in unitCube (ι := Fin n), K ^ 2 * (∏ i : Fin c.length,
          (if c.partSize i ≤ M then max 1 A
           else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2
        ≤ K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)) := by
    intro c
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_prod_block_bound hM P hPsm A Etop hEtop hPl2 c) (by positivity)
  calc ∫ x in unitCube (ι := Fin n),
        ‖pdVec (s + 1) l (fun x => Ψ (x, P x)) x‖ ^ 2
      = ∫ x in unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ (s + 1) (fun x : Fin n → ℝ => Ψ (x, P x)) x
            (fun j => Pi.single (l j) (1 : ℝ))‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => congrArg (fun z => ‖z‖ ^ 2) (hpd x))
    _ ≤ ∫ x in unitCube (ι := Fin n),
          N * ∑ c : OrderedFinpartition (s + 1),
            K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
        integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
          (el_integrableOn_unitCube_of_continuous_real hcontR)
          (Filter.Eventually.of_forall hpt)
    _ = N * ∫ x in unitCube (ι := Fin n),
          ∑ c : OrderedFinpartition (s + 1),
            K ^ 2 * (∏ i : Fin c.length,
              (if c.partSize i ≤ M then max 1 A
               else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 :=
        integral_const_mul _ _
    _ = N * ∑ c : OrderedFinpartition (s + 1),
          ∫ x in unitCube (ι := Fin n), K ^ 2 * (∏ i : Fin c.length,
            (if c.partSize i ≤ M then max 1 A
             else max 1 ‖iteratedFDeriv ℝ (c.partSize i) P x‖)) ^ 2 := by
        rw [integral_finsetSum _ fun c _ =>
          el_integrableOn_unitCube_of_continuous_real (hfacs c)]
    _ ≤ N * ∑ _c : OrderedFinpartition (s + 1),
          K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hper c) hN0
    _ = N * ((Fintype.card (OrderedFinpartition (s + 1)) : ℝ)
          * (K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
          * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by
        rw [hNdef] at *
        have hmax : max 1 A ≤ 1 + A := by
          rcases le_total 1 A with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        have hmax0 : 0 ≤ max 1 A := by positivity
        have h1A : 1 ≤ 1 + A := by linarith
        have hpow : (max 1 A) ^ (2 * (s + 1)) ≤ (1 + A) ^ (2 * (s + 2)) := by
          calc (max 1 A) ^ (2 * (s + 1)) ≤ (1 + A) ^ (2 * (s + 1)) :=
                pow_le_pow_left₀ hmax0 hmax _
            _ ≤ (1 + A) ^ (2 * (s + 2)) :=
                pow_le_pow_right₀ h1A (by omega)
        have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
        have hEt : 0 ≤ 1 + Etop := by linarith
        have hNc : 0 ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) := Nat.cast_nonneg _
        have hmain : (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop))
            ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((1 + A) ^ (2 * (s + 2)) * (1 + Etop)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hEt) (by positivity)
        calc (Fintype.card (OrderedFinpartition (s + 1)) : ℝ)
              * ((Fintype.card (OrderedFinpartition (s + 1)) : ℝ)
                * (K ^ 2 * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop))))
            = (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((max 1 A) ^ (2 * (s + 1)) * (1 + Etop)) := by ring
          _ ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * ((1 + A) ^ (2 * (s + 2)) * (1 + Etop)) := hmain
          _ = (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) ^ 2 * K ^ 2
              * (1 + A) ^ (2 * (s + 2)) * (1 + Etop) := by ring

end Work.Diff.STE.flat
