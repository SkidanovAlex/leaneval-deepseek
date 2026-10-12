import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Assembly
import Submission.Work.BoseFixB2.DvApriori.Band.SumSecProjTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.UniversalTwo`

The `k = 2` analogue of `Work.BoseFixB2.DvApriori.band_sum_eq_sum_projOn`: for a weight `W`
that is constant along all slots outside a slot set `A`,

    Σ_{i<n-1} ⟨1_{n₊=i}Φ, W 1_{n₊=i+2}Φ⟩
      = Σ_{U,V ⊆ A, |V| = |U|+2} ⟨E_U^A Φ, W E_V^A Φ⟩,

together with its evaluation on a one-slot weight (`= 0`, no level can jump by two through a
single slot) and on a two-slot weight (the single term `U = ∅`, `V = {a,b}`).
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

/-- The `k = 2` band identity: the band-2 sum of pairings against `W` is the sum, over the
pairs of patterns of `A` differing by two slots, of the pairings of the `A`-localised
projections. -/
theorem bandFunTwo_eq_sum_projOn {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) {W : Submission.BoseGases.X n → ℝ}
    (hWint : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox n ℓ))
    (hWin : ∀ (j : ℕ) (hj : j < n), j ∉ A →
      ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFunTwo ℓ n W Φ
      = ∑ U ∈ A.powerset,
          ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 2),
            ∫ x in Submission.BoseGases.abox n ℓ,
              projOn ℓ A U Φ x * W x * projOn ℓ A V Φ x := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hJ : (Finset.range n \ A) ∪ A = Finset.range n := by
    ext j; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro (⟨hj, _⟩ | hj); exacts [hj, Finset.mem_range.mp (hA hj)]
    · intro hj; by_cases h : j ∈ A
      · exact Or.inr h
      · exact Or.inl ⟨hj, h⟩
  have hdisj : Disjoint (Finset.range n \ A) A := Finset.disjoint_sdiff.symm
  rw [show bandFunTwo ℓ n W Φ = ∑ i ∈ Finset.range (n-1),
        ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+2) Φ x from rfl]
  rw [Work.BoseFixB2.DvApriori.Band.sum_secProj_eq_sum_triples_two hℓ hA hWint hΦ
    (fun S T hS hT hST =>
      Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne hℓ hA
        (fun j hj hjA x z => hWin j hj hjA x z) hS hT hST hΦ
        (Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
          (Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦc)
          (Work.BoseFixB2.Sector.jointProj_continuous hℓ T hΦc) hWint))]
  have hswap : (∑ R ∈ (Finset.range n \ A).powerset, ∑ U ∈ A.powerset,
        ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 2),
          ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseFixB2.jointProj ℓ (R ∪ U) Φ x * W x
              * Work.BoseFixB2.jointProj ℓ (R ∪ V) Φ x)
      = ∑ U ∈ A.powerset, ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 2),
          ∑ R ∈ (Finset.range n \ A).powerset,
            ∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseFixB2.jointProj ℓ (R ∪ U) Φ x * W x
                * Work.BoseFixB2.jointProj ℓ (R ∪ V) Φ x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun U hU => ?_)
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl (fun U hU => Finset.sum_congr rfl (fun V hV => ?_))
  exact Work.BoseFixB2.DvApriori.sum_jointProj_pairing (A := A) (J := Finset.range n \ A) hℓ
    (by rw [Finset.union_comm]; exact hJ) hdisj.symm
    (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp ((Finset.mem_filter.mp hV).1))
    (fun j hj hjJ x z => hWin j hj (fun h => (Finset.mem_sdiff.mp hjJ).2 h) x z) hWint hΦc

/-- **Linearity of the band-2 functional in a scalar multiple of the weight.** -/
lemma bandFunTwo_const_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (c : ℝ)
    (W : Submission.BoseGases.X n → ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    bandFunTwo ℓ n (fun x => c * W x) Φ = c * bandFunTwo ℓ n W Φ := by
  unfold bandFunTwo
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * (c * W x) * Work.BoseFixB2.secProj ℓ (i+2) Φ x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        c * (Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+2) Φ x) from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring]
  rw [MeasureTheory.integral_const_mul]

/-- **Linearity of the band-2 functional in the weight, two-term form.** -/
lemma bandFunTwo_add {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {W₁ W₂ : Submission.BoseGases.X n → ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (h₁ : MeasureTheory.IntegrableOn W₁ (Submission.BoseGases.abox n ℓ))
    (h₂ : MeasureTheory.IntegrableOn W₂ (Submission.BoseGases.abox n ℓ)) :
    bandFunTwo ℓ n (fun x => W₁ x + W₂ x) Φ = bandFunTwo ℓ n W₁ Φ + bandFunTwo ℓ n W₂ Φ := by
  unfold bandFunTwo
  have h1 : ∀ i : ℕ, (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * (W₁ x + W₂ x) * Work.BoseFixB2.secProj ℓ (i+2) Φ x)
      = (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * W₁ x * Work.BoseFixB2.secProj ℓ (i+2) Φ x)
        + (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * W₂ x * Work.BoseFixB2.secProj ℓ (i+2) Φ x) := by
    intro i
    have hpt : (fun x : Submission.BoseGases.X n =>
          Work.BoseFixB2.secProj ℓ i Φ x * (W₁ x + W₂ x) * Work.BoseFixB2.secProj ℓ (i+2) Φ x)
        = fun x => (Work.BoseFixB2.secProj ℓ i Φ x * W₁ x
              * Work.BoseFixB2.secProj ℓ (i+2) Φ x)
            + (Work.BoseFixB2.secProj ℓ i Φ x * W₂ x
                * Work.BoseFixB2.secProj ℓ (i+2) Φ x) := by
      funext x; ring
    rw [hpt]
    exact MeasureTheory.integral_add
      (Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (secProj_continuous' hℓ hΦ i) (secProj_continuous' hℓ hΦ (i+2)) h₁)
      (Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (secProj_continuous' hℓ hΦ i) (secProj_continuous' hℓ hΦ (i+2)) h₂)
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]

/-- **Linearity of the band-2 functional in a finite sum of weights.** -/
lemma bandFunTwo_finsetSum {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {ι : Type*} (s : Finset ι)
    {T : ι → Submission.BoseGases.X n → ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) (hT : ∀ e ∈ s, MeasureTheory.IntegrableOn (T e) (Submission.BoseGases.abox n ℓ)) :
    bandFunTwo ℓ n (fun x => ∑ e ∈ s, T e x) Φ = ∑ e ∈ s, bandFunTwo ℓ n (T e) Φ := by
  unfold bandFunTwo
  have h1 : ∀ i : ℕ, (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * (∑ e ∈ s, T e x)
          * Work.BoseFixB2.secProj ℓ (i+2) Φ x)
      = ∑ e ∈ s, ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * T e x * Work.BoseFixB2.secProj ℓ (i+2) Φ x := by
    intro i
    have hpt : ∀ x : Submission.BoseGases.X n,
        Work.BoseFixB2.secProj ℓ i Φ x * (∑ e ∈ s, T e x)
            * Work.BoseFixB2.secProj ℓ (i+2) Φ x
          = ∑ e ∈ s,
              Work.BoseFixB2.secProj ℓ i Φ x * T e x
                * Work.BoseFixB2.secProj ℓ (i+2) Φ x := by
      intro x
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_finsetSum _ (fun e he =>
      Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (secProj_continuous' hℓ hΦ i) (secProj_continuous' hℓ hΦ (i+2)) (hT e he))
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]

/-! ## The `(U,V)`-sum over a two-element slot set for `k = 2` -/

/-- **The `(U,V)`-sum for a two-element slot set, `k = 2`**: only `U = ∅`, `V = {a,b}`
survives. -/
lemma sum_pair_powersetCard_two {a b : ℕ} (hab : a ≠ b) (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ U ∈ ({a, b} : Finset ℕ).powerset,
        ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (U.card + 2), F U V)
      = F ∅ {a, b} := by
  have hcard : ({a, b} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hab),
      Finset.card_singleton]
  refine Finset.sum_eq_single (∅ : Finset ℕ) ?_ ?_ |>.trans ?_
  · intro U hU hUne
    rw [Finset.powersetCard_eq_empty.mpr (by
      have h1 : 0 < U.card := by
        rcases Finset.eq_empty_or_nonempty U with h | ⟨x, hx⟩
        · exact absurd h hUne
        · exact Finset.card_pos.mpr ⟨x, hx⟩
      omega)]
    simp
  · intro h
    exact absurd (Finset.mem_powerset.mpr (Finset.empty_subset _)) h
  · show (∑ V ∈ ({a, b} : Finset ℕ).powersetCard ((∅ : Finset ℕ).card + 2), F ∅ V)
      = F ∅ {a, b}
    rw [Finset.card_empty, zero_add, ← hcard, Finset.powersetCard_self, Finset.sum_singleton]

/-- **Evaluation of the band-2 functional on a two-slot weight**: the only transition is
`∅ → {a,b}`. -/
lemma bandFunTwo_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (i : Fin n), i ≠ a → i ≠ b → ∀ (x : Submission.BoseGases.X n)
      (z : EuclideanSpace ℝ (Fin 3)), W (Function.update x i z) = W x)
    (hWi : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox n ℓ))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFunTwo ℓ n W Φ
      = ∫ x in Submission.BoseGases.abox n ℓ,
          aP ℓ a (aP ℓ b Φ) x * W x * aQ ℓ a (aQ ℓ b Φ) x := by
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hA : ({a.val, b.val} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_insert.mp hk with h | h
    · rw [h]; exact Finset.mem_range.mpr a.isLt
    · rw [Finset.mem_singleton.mp h]; exact Finset.mem_range.mpr b.isLt
  have h := bandFunTwo_eq_sum_projOn (ℓ := ℓ) (n := n) (A := {a.val, b.val}) hℓ hA hWi
    (fun i hi hiA x z =>
      hWin ⟨i, hi⟩
        (fun hcon => hiA (Finset.mem_insert.mpr (Or.inl (by
          have := congrArg Fin.val hcon; simpa using this))))
        (fun hcon => hiA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by
          have := congrArg Fin.val hcon; simpa using this))))) x z) hΦ
  rw [h]
  rw [show (∑ U ∈ ({a.val, b.val} : Finset ℕ).powerset,
        ∑ V ∈ ({a.val, b.val} : Finset ℕ).powerset.filter (fun V => V.card = U.card + 2),
          ∫ x in Submission.BoseGases.abox n ℓ, projOn ℓ {a.val, b.val} U Φ x * W x
            * projOn ℓ {a.val, b.val} V Φ x)
      = ∑ U ∈ ({a.val, b.val} : Finset ℕ).powerset,
        ∑ V ∈ ({a.val, b.val} : Finset ℕ).powersetCard (U.card + 2),
          ∫ x in Submission.BoseGases.abox n ℓ, projOn ℓ {a.val, b.val} U Φ x * W x
            * projOn ℓ {a.val, b.val} V Φ x from
    Finset.sum_congr rfl (fun U _ => by rw [← Finset.powersetCard_eq_filter])]
  rw [sum_pair_powersetCard_two habv (fun U V => ∫ x in Submission.BoseGases.abox n ℓ,
    projOn ℓ {a.val, b.val} U Φ x * W x * projOn ℓ {a.val, b.val} V Φ x)]
  have h1 : projOn ℓ {a.val, b.val} ∅ Φ = aP ℓ a (aP ℓ b Φ) := by
    rw [projOn_pair hℓ a b hab ∅ hΦ.continuous]; simp
  have h4 : projOn ℓ {a.val, b.val} {a.val, b.val} Φ = aQ ℓ a (aQ ℓ b Φ) := by
    rw [projOn_pair hℓ a b hab {a.val, b.val} hΦ.continuous]
    simp
  rw [h1, h4]

/-- **Evaluation of the band-2 functional on a one-slot weight**: it vanishes, since a single
slot cannot supply the two level jumps. -/
lemma bandFunTwo_single {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (i : Fin n), i ≠ j → ∀ (x : Submission.BoseGases.X n)
      (z : EuclideanSpace ℝ (Fin 3)), W (Function.update x i z) = W x)
    (hWi : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox n ℓ))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFunTwo ℓ n W Φ = 0 := by
  have hA : ({j.val} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_singleton] at hk
    rw [hk]
    exact Finset.mem_range.mpr j.isLt
  rw [bandFunTwo_eq_sum_projOn (ℓ := ℓ) (n := n) (A := {j.val}) hℓ hA hWi
    (fun i hi hiA x z => hWin ⟨i, hi⟩ (fun hcon => hiA (Finset.mem_singleton.mpr (by
      have := congrArg Fin.val hcon; simpa using this))) x z) hΦ]
  refine Finset.sum_eq_zero (fun U hU => Finset.sum_eq_zero (fun V hV => ?_))
  exfalso
  rw [Finset.mem_filter] at hV
  have hU1 : U.card ≤ 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp hU)
    simpa [Finset.card_singleton] using h
  have hV1 : V.card ≤ 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp hV.1)
    simpa [Finset.card_singleton] using h
  omega

end

end Work.BoseFixB2.DvApriori
