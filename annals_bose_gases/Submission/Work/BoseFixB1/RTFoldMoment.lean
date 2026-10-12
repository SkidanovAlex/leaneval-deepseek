import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.RTFoldFact
import Submission.Work.BoseFixB1.sum_flatPieceRT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The index set of disjoint pairs -/

/-- **The index set of the flat family**: the pairs `(S,T)` of slot sets with `T ⊆ Sᶜ`. -/
def pairIdx (N : ℕ) : Finset ((Finset (Fin N)) × (Finset (Fin N))) :=
  ((Finset.univ : Finset (Finset (Fin N))) ×ˢ (Finset.univ : Finset (Finset (Fin N)))).filter
    (fun p => p.2 ∈ p.1ᶜ.powerset)

/-- Membership in `pairIdx N` is the disjointness of the pair. -/
theorem mem_pairIdx {N : ℕ} {p : (Finset (Fin N)) × (Finset (Fin N))} :
    p ∈ pairIdx N ↔ p.2 ⊆ p.1ᶜ := by
  simp [pairIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]

/-- The double sum over `pairIdx N` is the iterated sum over `S` and `T ⊆ Sᶜ`. -/
theorem pairIdx_sum {N : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Finset (Fin N) → Finset (Fin N) → M) :
    (∑ p ∈ pairIdx N, f p.1 p.2) = ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, f S T := by
  rw [pairIdx, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  show (∑ y : Finset (Fin N), if y ∈ Sᶜ.powerset then f S y else 0)
      = ∑ T ∈ Sᶜ.powerset, f S T
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Every function on the pairs which is `IntegrableOn` the box is summable on a finite family. -/
theorem integrableOn_finset_sum {N : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι)
    {F : ι → X N → ℝ} (hF : ∀ i ∈ s, IntegrableOn (F i) (abox N ℓ) volume) :
    IntegrableOn (fun x => ∑ i ∈ s, F i x) (abox N ℓ) volume := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h : (fun x => ∑ i ∈ insert a s, F i x) = fun x => F a x + ∑ i ∈ s, F i x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [h]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-! ## 2. A uniform bound on the pieces

The pieces are built from `N` one-slot operators, each of which costs at most a factor `2` on the
box, so `2^N·C` bounds *every* piece whenever `C` bounds the state.  This uniform bound is what
makes the slot operators additive on the whole flat family. -/

/-- **A list-length uniform bound on the fold** (used only at `l = List.finRange N`). -/
theorem flatPieceRTList_abs_le {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ) :
    ∀ (l : List (Fin N)) (S T : Finset (Fin N)) {f : X N → ℝ} {C : ℝ}, 0 ≤ C →
      (∀ x ∈ abox N ℓ, |f x| ≤ C) →
      ∀ x ∈ abox N ℓ, |flatPieceRTList V A l S T f x| ≤ 2 ^ l.length * C := by
  intro l
  induction l with
  | nil =>
    intro S T f C hC0 hCb x hx
    simpa using hCb x hx
  | cons i l' ih =>
    intro S T f C hC0 hCb x hx
    have htail : ∀ y ∈ abox N ℓ, |flatPieceRTList V A l' S T f y| ≤ 2 ^ l'.length * C :=
      fun y hy => ih S T hC0 hCb y hy
    have hM0 : 0 ≤ 2 ^ l'.length * C := mul_nonneg (by positivity) hC0
    rw [flatPieceRTList_cons]
    by_cases hiS : i ∈ S
    · rw [if_pos hiS]
      calc |Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l' S T f) x|
          ≤ 2 ^ l'.length * C := Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i htail x hx
        _ ≤ 2 ^ (i :: l').length * C := by
              rw [List.length_cons]
              calc 2 ^ l'.length * C ≤ 2 * (2 ^ l'.length * C) :=
                    le_mul_of_one_le_left hM0 (by norm_num)
                _ = 2 ^ (l'.length + 1) * C := by ring
    · rw [if_neg hiS]
      by_cases hiT : i ∈ T
      · rw [if_pos hiT]
        calc |Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l' S T f) x|
            ≤ 2 * (2 ^ l'.length * C) := abs_boxQInd_le_abox hℓ hV hA hVeq hAc i htail x hx
          _ = 2 ^ (i :: l').length * C := by
              rw [List.length_cons, pow_succ]
              ring
      · rw [if_neg hiT]
        calc |rInd A i (flatPieceRTList V A l' S T f) x|
            ≤ 2 ^ l'.length * C := le_trans (abs_rInd_le A i _ x) (htail x hx)
          _ ≤ 2 ^ (i :: l').length * C := by
              rw [List.length_cons]
              calc 2 ^ l'.length * C ≤ 2 * (2 ^ l'.length * C) :=
                    le_mul_of_one_le_left hM0 (by norm_num)
                _ = 2 ^ (l'.length + 1) * C := by ring

/-- **The uniform bound on the flat family**: if `C` bounds `Φ` on the box then `2^N·C` bounds
every piece `Θ_{S,T}Φ` there. -/
theorem flatPieceRT_uniform_abs_le {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hCb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) :
    ∀ (S T : Finset (Fin N)) (x : X N), x ∈ abox N ℓ →
      |flatPieceRT V A S T Φ x| ≤ 2 ^ N * C := by
  intro S T x hx
  have h := flatPieceRTList_abs_le hℓ hV hA hVeq hAc (List.finRange N) S T hC0 hCb x hx
  simpa [flatPieceRT, List.length_finRange] using h

/-! ## 3. The Parseval identity of the flat family -/

/-- **Parseval identity.**  For arbitrary real weights `c`, `d` on the disjoint pairs,

  `∫ (Σ_p c_p Θ_p)·(Σ_q d_q Θ_q) = Σ_p c_p d_p ∫ Θ_p²`.

The expansion of the product produces the doubly indexed sum `Σ_p Σ_q c_p d_q ∫Θ_pΘ_q`, whose
off-diagonal terms vanish by `flatPieceRT_orthogonal`. -/
theorem flatPieceRT_parseval {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (c d : (Finset (Fin N)) × (Finset (Fin N)) → ℝ) :
    (∫ x in abox N ℓ, (∑ p ∈ pairIdx N, c p * flatPieceRT V A p.1 p.2 Φ x)
        * (∑ q ∈ pairIdx N, d q * flatPieceRT V A q.1 q.2 Φ x))
      = ∑ p ∈ pairIdx N, c p * d p
          * ∫ x in abox N ℓ, (flatPieceRT V A p.1 p.2 Φ x) ^ 2 := by
  obtain ⟨C, hC0, hCb⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hunif : ∀ (S T : Finset (Fin N)) (x : X N), x ∈ abox N ℓ →
      |flatPieceRT V A S T Φ x| ≤ 2 ^ N * C :=
    flatPieceRT_uniform_abs_le hℓ hV hA hVeq hAc hC0 hCb
  have hmeas : ∀ S T : Finset (Fin N), Measurable (flatPieceRT V A S T Φ) :=
    fun S T => (flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S T).1
  -- integrability of a single product term
  have hint : ∀ p ∈ pairIdx N, ∀ q ∈ pairIdx N,
      IntegrableOn (fun x => (c p * flatPieceRT V A p.1 p.2 Φ x)
        * (d q * flatPieceRT V A q.1 q.2 Φ x)) (abox N ℓ) volume := by
    intro p _ q _
    refine Work.BoseFixB1S.integrableOn_mul_of_bound hℓ ((hmeas p.1 p.2).const_mul (c p))
      ((hmeas q.1 q.2).const_mul (d q))
      (Cf := |c p| * (2 ^ N * C)) (Cg := |d q| * (2 ^ N * C)) ?_ ?_
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hunif p.1 p.2 x hx) (abs_nonneg _)
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hunif q.1 q.2 x hx) (abs_nonneg _)
  have h1 : (∫ x in abox N ℓ, (∑ p ∈ pairIdx N, c p * flatPieceRT V A p.1 p.2 Φ x)
        * (∑ q ∈ pairIdx N, d q * flatPieceRT V A q.1 q.2 Φ x))
      = ∫ x in abox N ℓ, ∑ p ∈ pairIdx N, ∑ q ∈ pairIdx N,
          (c p * flatPieceRT V A p.1 p.2 Φ x) * (d q * flatPieceRT V A q.1 q.2 Φ x) := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x _
    show (∑ p ∈ pairIdx N, c p * flatPieceRT V A p.1 p.2 Φ x)
        * (∑ q ∈ pairIdx N, d q * flatPieceRT V A q.1 q.2 Φ x)
      = ∑ p ∈ pairIdx N, ∑ q ∈ pairIdx N,
          (c p * flatPieceRT V A p.1 p.2 Φ x) * (d q * flatPieceRT V A q.1 q.2 Φ x)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
  have h2 : (∫ x in abox N ℓ, ∑ p ∈ pairIdx N, ∑ q ∈ pairIdx N,
        (c p * flatPieceRT V A p.1 p.2 Φ x) * (d q * flatPieceRT V A q.1 q.2 Φ x))
      = ∑ p ∈ pairIdx N, ∑ q ∈ pairIdx N,
          ∫ x in abox N ℓ, (c p * flatPieceRT V A p.1 p.2 Φ x)
            * (d q * flatPieceRT V A q.1 q.2 Φ x) := by
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [integral_finset_sum]
      intro q hq
      exact hint p (by assumption) q hq
    · intro p hp
      exact integrableOn_finset_sum _ (fun q hq => hint p hp q hq)
  have h3 : ∀ p ∈ pairIdx N,
      (∑ q ∈ pairIdx N, ∫ x in abox N ℓ, (c p * flatPieceRT V A p.1 p.2 Φ x)
            * (d q * flatPieceRT V A q.1 q.2 Φ x))
        = c p * d p * ∫ x in abox N ℓ, (flatPieceRT V A p.1 p.2 Φ x) ^ 2 := by
    intro p hp
    have hsub : p.2 ⊆ p.1ᶜ := mem_pairIdx.mp hp
    rw [Finset.sum_eq_single p]
    · rw [show (∫ x in abox N ℓ, (c p * flatPieceRT V A p.1 p.2 Φ x)
            * (d p * flatPieceRT V A p.1 p.2 Φ x))
          = ∫ x in abox N ℓ, (c p * d p)
              * (flatPieceRT V A p.1 p.2 Φ x * flatPieceRT V A p.1 p.2 Φ x) from by
        apply setIntegral_congr_fun (abox_measurable N ℓ); intro x _; ring,
        MeasureTheory.integral_const_mul]
      congr 1
      apply setIntegral_congr_fun (abox_measurable N ℓ)
      intro x _
      ring
    · intro q hq hqp
      have hsub' : q.2 ⊆ q.1ᶜ := mem_pairIdx.mp hq
      have hne : (p.1, p.2) ≠ (q.1, q.2) := fun h =>
        hqp (Prod.ext (Prod.mk.inj h).1.symm (Prod.mk.inj h).2.symm)
      rw [show (∫ x in abox N ℓ, (c p * flatPieceRT V A p.1 p.2 Φ x)
            * (d q * flatPieceRT V A q.1 q.2 Φ x))
          = (c p * d q) * ∫ x in abox N ℓ,
              flatPieceRT V A p.1 p.2 Φ x * flatPieceRT V A q.1 q.2 Φ x from by
        rw [← MeasureTheory.integral_const_mul]
        apply setIntegral_congr_fun (abox_measurable N ℓ); intro x _; ring,
        flatPieceRT_orthogonal hℓ hV hA hVeq hAc hΦc p.1 p.2 q.1 q.2 hsub hsub' hne,
        mul_zero]
    · intro hp'
      exact absurd hp hp'
  rw [h1, h2]
  exact Finset.sum_congr rfl (fun p hp => h3 p hp)

/-! ## 4. The two slot-count identities -/

/-- **`P_i` reads off the number of `i`-slots in the flat family**: the `i`-th weight sum of the
family is `P_iΦ`. -/
theorem pairIdx_boxPInd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) {x : X N} (hx : x ∈ abox N ℓ) :
    (∑ p ∈ pairIdx N, (if i ∈ p.1 then flatPieceRT V A p.1 p.2 Φ x else 0))
      = Work.UBBInputs8.boxPInd V A i Φ x := by
  obtain ⟨C, hC0, hCb⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hK0 : 0 ≤ 2 ^ N * C := mul_nonneg (by positivity) hC0
  have hunif : ∀ (S T : Finset (Fin N)) (x : X N), x ∈ abox N ℓ →
      |flatPieceRT V A S T Φ x| ≤ 2 ^ N * C :=
    flatPieceRT_uniform_abs_le hℓ hV hA hVeq hAc hC0 hCb
  have hmeas : ∀ S T : Finset (Fin N), Measurable (flatPieceRT V A S T Φ) :=
    fun S T => (flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S T).1
  have h1 : (∑ p ∈ pairIdx N, (if i ∈ p.1 then flatPieceRT V A p.1 p.2 Φ x else 0))
      = ∑ p ∈ pairIdx N,
          Work.UBBInputs8.boxPInd V A i (flatPieceRT V A p.1 p.2 Φ) x := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hsub : p.2 ⊆ p.1ᶜ := mem_pairIdx.mp hp
    have hdisj : Disjoint p.1 p.2 := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Finset.mem_compl.mp (hsub hb)) ha
    exact ((flatPieceRT_eigen_box hℓ hV hA hVeq hAc hΦc p.1 p.2 hdisj i).1 x hx).symm
  rw [h1, ← boxPInd_finset_sum hℓ V hA hAc (pairIdx N) hK0
    (fun p _ => hmeas p.1 p.2) (fun p _ y hy => hunif p.1 p.2 y hy) hx]
  exact (boxInd_congr_on (V := V) hA hAc i hx (fun y hy => by
    rw [pairIdx_sum (f := fun S T => flatPieceRT V A S T Φ y)]
    exact Work.BoseFixB1.sum_flatPieceRT hℓ hV hA hVeq hAc hΦc y)).1

/-- **`Q_j` reads off the number of `j`-slots in the flat family**. -/
theorem pairIdx_boxQInd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (j : Fin N) {x : X N} (hx : x ∈ abox N ℓ) :
    (∑ p ∈ pairIdx N, (if j ∈ p.2 then flatPieceRT V A p.1 p.2 Φ x else 0))
      = Work.UBBInputs8.boxQInd V A j Φ x := by
  obtain ⟨C, hC0, hCb⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hK0 : 0 ≤ 2 ^ N * C := mul_nonneg (by positivity) hC0
  have hunif : ∀ (S T : Finset (Fin N)) (x : X N), x ∈ abox N ℓ →
      |flatPieceRT V A S T Φ x| ≤ 2 ^ N * C :=
    flatPieceRT_uniform_abs_le hℓ hV hA hVeq hAc hC0 hCb
  have hmeas : ∀ S T : Finset (Fin N), Measurable (flatPieceRT V A S T Φ) :=
    fun S T => (flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S T).1
  have h1 : (∑ p ∈ pairIdx N, (if j ∈ p.2 then flatPieceRT V A p.1 p.2 Φ x else 0))
      = ∑ p ∈ pairIdx N,
          Work.UBBInputs8.boxQInd V A j (flatPieceRT V A p.1 p.2 Φ) x := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hsub : p.2 ⊆ p.1ᶜ := mem_pairIdx.mp hp
    have hdisj : Disjoint p.1 p.2 := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Finset.mem_compl.mp (hsub hb)) ha
    exact ((flatPieceRT_eigen_box hℓ hV hA hVeq hAc hΦc p.1 p.2 hdisj j).2.1 x hx).symm
  rw [h1, ← boxQInd_finset_sum hℓ V hA hAc (pairIdx N) hK0
    (fun p _ => hmeas p.1 p.2) (fun p _ y hy => hunif p.1 p.2 y hy) hx]
  exact (boxInd_congr_on (V := V) hA hAc j hx (fun y hy => by
    rw [pairIdx_sum (f := fun S T => flatPieceRT V A S T Φ y)]
    exact Work.BoseFixB1.sum_flatPieceRT hℓ hV hA hVeq hAc hΦc y)).2

/-- **The number operator `n₀ = Σ_i P_i` is the `|S|`-weight of the flat family** on the box. -/
theorem flatPieceRT_rungF_eq {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    ∀ x ∈ abox N ℓ,
      (∑ p ∈ pairIdx N, (p.1.card : ℝ) * flatPieceRT V A p.1 p.2 Φ x)
        = Work.BoseFixB1.rungF V A Φ x := by
  intro x hx
  calc (∑ p ∈ pairIdx N, (p.1.card : ℝ) * flatPieceRT V A p.1 p.2 Φ x)
      = ∑ p ∈ pairIdx N, ∑ i ∈ p.1, flatPieceRT V A p.1 p.2 Φ x :=
        Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ p ∈ pairIdx N, ∑ i : Fin N,
          (if i ∈ p.1 then flatPieceRT V A p.1 p.2 Φ x else 0) :=
        Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_ite_mem, Finset.univ_inter])
    _ = ∑ i : Fin N, ∑ p ∈ pairIdx N,
          (if i ∈ p.1 then flatPieceRT V A p.1 p.2 Φ x else 0) := Finset.sum_comm
    _ = ∑ i : Fin N, Work.UBBInputs8.boxPInd V A i Φ x :=
        Finset.sum_congr rfl (fun i _ => pairIdx_boxPInd hℓ hV hA hVeq hAc hΦc i hx)
    _ = Work.BoseFixB1.rungF V A Φ x := rfl

/-- **The number operator `n₊ = Σ_j Q_j` is the `|T|`-weight of the flat family** on the box. -/
theorem sum_boxQInd_eq {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    ∀ x ∈ abox N ℓ,
      (∑ j : Fin N, Work.UBBInputs8.boxQInd V A j Φ x)
        = ∑ p ∈ pairIdx N, (p.2.card : ℝ) * flatPieceRT V A p.1 p.2 Φ x := by
  intro x hx
  calc (∑ j : Fin N, Work.UBBInputs8.boxQInd V A j Φ x)
      = ∑ j : Fin N, ∑ p ∈ pairIdx N,
          (if j ∈ p.2 then flatPieceRT V A p.1 p.2 Φ x else 0) :=
        Finset.sum_congr rfl (fun j _ => (pairIdx_boxQInd hℓ hV hA hVeq hAc hΦc j hx).symm)
    _ = ∑ p ∈ pairIdx N, ∑ j : Fin N,
          (if j ∈ p.2 then flatPieceRT V A p.1 p.2 Φ x else 0) := Finset.sum_comm
    _ = ∑ p ∈ pairIdx N, ∑ j ∈ p.2, flatPieceRT V A p.1 p.2 Φ x :=
        Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_ite_mem, Finset.univ_inter])
    _ = ∑ p ∈ pairIdx N, (p.2.card : ℝ) * flatPieceRT V A p.1 p.2 Φ x :=
        Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_const, nsmul_eq_mul])

end Work.BoseFixB1
