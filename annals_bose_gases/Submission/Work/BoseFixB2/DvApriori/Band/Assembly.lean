import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Small
import Submission.Work.BoseFixB2.DvApriori.Band.Universal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.Assembly`

The **band functional** `bandFun ℓ n W Φ = Σᵢ ∫_{abox} (1_{n₊=i}Φ)·W·(1_{n₊=i+1}Φ)`, its
linearity in the weight, and its evaluation on the two kinds of few-slot weights that make
up `potWordU` (a single-slot weight and a pair weight), together with the band-`2`
functional `bandFunTwo`.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- The band-`1` functional of the box word: the sum of the first off-diagonal pairings of
the `n₊`-grading against the multiplication operator `W`. -/
noncomputable def bandFun (ℓ : ℝ) (n : ℕ) (W : Submission.BoseGases.X n → ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∫ x in abox n ℓ,
    Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+1) Φ x

/-- The band-`2` functional of the box word. -/
noncomputable def bandFunTwo (ℓ : ℝ) (n : ℕ) (W : Submission.BoseGases.X n → ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n-1), ∫ x in abox n ℓ,
    Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+2) Φ x

lemma secProj_continuous' {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) (k : ℕ) : Continuous (Work.BoseFixB2.secProj ℓ k Φ) := by
  rw [Work.BoseFixB2.secProj]
  rw [show (∑ S ∈ (Finset.range n).powersetCard k, Work.BoseFixB2.jointProj ℓ S Φ)
      = fun a : Submission.BoseGases.X n =>
          ∑ S ∈ (Finset.range n).powersetCard k, Work.BoseFixB2.jointProj ℓ S Φ a from by
    funext a
    rw [Finset.sum_apply]]
  exact continuous_finsetSum _ (fun S _ =>
    Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ)

/-- **Linearity of the band functional in the weight.** -/
lemma bandFun_finsetSum {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {ι : Type*} (s : Finset ι)
    {T : ι → Submission.BoseGases.X n → ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) (hT : ∀ e ∈ s, IntegrableOn (T e) (abox n ℓ)) :
    bandFun ℓ n (fun x => ∑ e ∈ s, T e x) Φ = ∑ e ∈ s, bandFun ℓ n (T e) Φ := by
  unfold bandFun
  have h1 : ∀ i : ℕ, (∫ x in abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * (∑ e ∈ s, T e x) * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      = ∑ e ∈ s, ∫ x in abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * T e x * Work.BoseFixB2.secProj ℓ (i+1) Φ x := by
    intro i
    have hpt : ∀ x : Submission.BoseGases.X n,
        Work.BoseFixB2.secProj ℓ i Φ x * (∑ e ∈ s, T e x) * Work.BoseFixB2.secProj ℓ (i+1) Φ x
          = ∑ e ∈ s,
              Work.BoseFixB2.secProj ℓ i Φ x * T e x * Work.BoseFixB2.secProj ℓ (i+1) Φ x := by
      intro x
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_finsetSum _ (fun e he =>
      Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (secProj_continuous' hℓ hΦ i) (secProj_continuous' hℓ hΦ (i+1)) (hT e he))
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]

/-- Linearity of the band functional in the weight, two-term form. -/
lemma bandFun_add {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {W₁ W₂ : Submission.BoseGases.X n → ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (h₁ : IntegrableOn W₁ (abox n ℓ)) (h₂ : IntegrableOn W₂ (abox n ℓ)) :
    bandFun ℓ n (fun x => W₁ x + W₂ x) Φ = bandFun ℓ n W₁ Φ + bandFun ℓ n W₂ Φ := by
  unfold bandFun
  have h1 : ∀ i : ℕ, (∫ x in abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * (W₁ x + W₂ x) * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      = (∫ x in abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * W₁ x * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
        + (∫ x in abox n ℓ,
          Work.BoseFixB2.secProj ℓ i Φ x * W₂ x * Work.BoseFixB2.secProj ℓ (i+1) Φ x) := by
    intro i
    have hpt : (fun x : Submission.BoseGases.X n =>
          Work.BoseFixB2.secProj ℓ i Φ x * (W₁ x + W₂ x) * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
        = fun x => (Work.BoseFixB2.secProj ℓ i Φ x * W₁ x * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
            + (Work.BoseFixB2.secProj ℓ i Φ x * W₂ x
                * Work.BoseFixB2.secProj ℓ (i+1) Φ x) := by
      funext x; ring
    rw [hpt]
    exact MeasureTheory.integral_add
      (Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (secProj_continuous' hℓ hΦ i) (secProj_continuous' hℓ hΦ (i+1)) h₁)
      (Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (secProj_continuous' hℓ hΦ i) (secProj_continuous' hℓ hΦ (i+1)) h₂)
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]

/-- The powerset of a singleton. -/
lemma powerset_singleton' {α : Type*} [DecidableEq α] (a : α) :
    ({a} : Finset α).powerset = insert ∅ {{a}} := by
  ext S
  rw [Finset.mem_powerset]
  constructor
  · intro h
    rcases Finset.subset_singleton_iff.mp h with h' | h'
    · exact Finset.mem_insert.mpr (Or.inl h')
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h'))
  · intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · rw [h']
      exact Finset.empty_subset _
    · rw [Finset.mem_singleton.mp h']

/-- **Evaluation on a single-slot weight.** -/
lemma bandFun_single {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (i : Fin n), i ≠ j → ∀ (x : Submission.BoseGases.X n)
      (z : EuclideanSpace ℝ (Fin 3)), W (Function.update x i z) = W x)
    (hWi : IntegrableOn W (abox n ℓ)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFun ℓ n W Φ = ∫ x in abox n ℓ, aP ℓ j Φ x * W x * aQ ℓ j Φ x := by
  have hA : ({j.val} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_singleton] at hk
    rw [hk]
    exact Finset.mem_range.mpr j.isLt
  have h := band_sum_eq_sum_projOn (A := {j.val}) hℓ hA hWi
    (fun i hi hiA x z =>
      hWin ⟨i, hi⟩ (fun hcon => hiA (Finset.mem_singleton.mpr (by
        have := congrArg Fin.val hcon
        simpa using this))) x z) hΦ
  rw [bandFun, h, powerset_singleton' j.val,
    Finset.sum_insert (by simp), Finset.sum_singleton]
  have hV0 : ((insert ∅ {{j.val}} : Finset (Finset ℕ)).filter
      (fun V => V.card = (∅ : Finset ℕ).card + 1)) = {{j.val}} := by
    ext V
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_empty, zero_add]
    constructor
    · rintro ⟨h | h, hc⟩
      · subst h; simp at hc
      · exact h
    · intro h
      exact ⟨Or.inr h, by rw [h, Finset.card_singleton]⟩
  have hV1 : ((insert ∅ {{j.val}} : Finset (Finset ℕ)).filter
      (fun V => V.card = ({j.val} : Finset ℕ).card + 1)) = ∅ := by
    ext V
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton, Finset.notMem_empty]
    constructor
    · rintro ⟨h | h, hc⟩
      · subst h; simp at hc
      · subst h; simp at hc
    · intro h; exact absurd h (by simp)
  rw [hV0, hV1, Finset.sum_singleton, Finset.sum_empty, add_zero,
    projOn_singleton hℓ j ∅ hΦ.continuous,
    projOn_singleton hℓ j {j.val} hΦ.continuous]
  simp


/-! ## The powerset of a two-element set -/

lemma powerset_pair_eq {a b : ℕ} (hab : a ≠ b) :
    (insert a (insert b (∅ : Finset ℕ))).powerset
      = insert ∅ (insert ({a} : Finset ℕ) (insert ({b} : Finset ℕ)
          (insert ({a, b} : Finset ℕ) (∅ : Finset (Finset ℕ))))) := by
  have hab' : ∀ x, x ∈ ({a, b} : Finset ℕ) ↔ x = a ∨ x = b := fun x => by
    rw [Finset.mem_insert, Finset.mem_singleton]
  ext S
  rw [Finset.mem_powerset]
  constructor
  · intro h
    have hmem : ∀ x ∈ S, x = a ∨ x = b := fun x hx => by
      have h1 := h hx
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at h1
      exact h1
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · have hS : S = {a, b} := by
          apply Finset.Subset.antisymm
          · intro x hx
            exact (hab' x).mpr (hmem x hx)
          · intro x hx
            rcases (hab' x).mp hx with h' | h'
            · rw [h']; exact ha
            · rw [h']; exact hb
        subst hS
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      · have hS : S = {a} := by
          apply Finset.Subset.antisymm
          · intro x hx
            rcases hmem x hx with h' | h'
            · rw [h']; exact Finset.mem_singleton_self _
            · exact absurd (h' ▸ hx) hb
          · intro x hx
            rw [Finset.mem_singleton.mp hx]
            exact ha
        subst hS
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · by_cases hb : b ∈ S
      · have hS : S = {b} := by
          apply Finset.Subset.antisymm
          · intro x hx
            rcases hmem x hx with h' | h'
            · exact absurd (h' ▸ hx) ha
            · rw [h']; exact Finset.mem_singleton_self _
          · intro x hx
            rw [Finset.mem_singleton.mp hx]
            exact hb
        subst hS
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _))
      · have hS : S = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          rcases hmem x hx with h' | h'
          · exact ha (h' ▸ hx)
          · exact hb (h' ▸ hx)
        subst hS
        exact Finset.mem_insert_self _ _
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hmem
    rcases hmem with h | h | h | h
    · subst h
      intro x hx; exact absurd hx (Finset.notMem_empty x)
    · subst h
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact Finset.mem_insert_self _ _
    · subst h
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · subst h
      intro x hx
      exact (hab' x).mpr (by
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr hx)

lemma filter_card_one_pair {a b : ℕ} (hab : a ≠ b) :
    ((insert ∅ (insert ({a} : Finset ℕ) (insert ({b} : Finset ℕ) (insert ({a, b} : Finset ℕ) (∅ : Finset (Finset ℕ)))))).filter (fun V => V.card = 1))
      = insert ({a} : Finset ℕ) (insert ({b} : Finset ℕ) (∅ : Finset (Finset ℕ))) := by
  ext V
  constructor
  · intro hV
    rw [Finset.mem_filter] at hV
    obtain ⟨hV, hc⟩ := hV
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hV
    rcases hV with h | h | h | h
    · rw [h] at hc; simp at hc
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h] at hc
      rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hab)] at hc
      simp at hc
  · intro hV
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hV
    rw [Finset.mem_filter]
    rcases hV with h | h
    · subst h
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by simp⟩
    · subst h
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
        by simp⟩

lemma filter_card_two_pair {a b : ℕ} (hab : a ≠ b) :
    ((insert ∅ (insert ({a} : Finset ℕ) (insert ({b} : Finset ℕ) (insert ({a, b} : Finset ℕ) (∅ : Finset (Finset ℕ)))))).filter (fun V => V.card = 2))
      = insert ({a, b} : Finset ℕ) (∅ : Finset (Finset ℕ)) := by
  ext V
  constructor
  · intro hV
    rw [Finset.mem_filter] at hV
    obtain ⟨hV, hc⟩ := hV
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hV
    rcases hV with h | h | h | h
    · rw [h] at hc; simp at hc
    · rw [h] at hc; simp at hc
    · rw [h] at hc; simp at hc
    · rw [h]
      exact Finset.mem_insert_self _ _
  · intro hV
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hV
    rw [Finset.mem_filter]
    subst hV
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))), by
        rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hab),
          Finset.card_singleton]⟩

lemma filter_card_three_pair {a b : ℕ} (hab : a ≠ b) :
    ((insert ∅ (insert ({a} : Finset ℕ) (insert ({b} : Finset ℕ) (insert ({a, b} : Finset ℕ) (∅ : Finset (Finset ℕ)))))).filter (fun V => V.card = 3))
      = (∅ : Finset (Finset ℕ)) := by
  ext V
  constructor
  · intro hV
    rw [Finset.mem_filter] at hV
    obtain ⟨hV, hc⟩ := hV
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hV
    rcases hV with h | h | h | h
    · rw [h] at hc; simp at hc
    · rw [h] at hc; simp at hc
    · rw [h] at hc; simp at hc
    · rw [h] at hc
      rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hab),
        Finset.card_singleton] at hc
      simp at hc
  · intro hV
    exact absurd hV (Finset.notMem_empty V)

/-- The reindexing of a `powerset` sum by cardinality (general finset). -/
lemma sum_powersetCard_eq_sum_powerset_gen {α : Type*} [DecidableEq α] {β : Type*}
    [AddCommMonoid β] (s : Finset α) (g : Finset α → β) :
    (∑ k ∈ Finset.range (s.card + 1), ∑ S ∈ s.powersetCard k, g S)
      = ∑ S ∈ s.powerset, g S := by
  have hmem : ∀ S ∈ s.powerset, S.card ∈ Finset.range (s.card + 1) := by
    intro S hS
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (by simpa using Finset.card_le_card (Finset.mem_powerset.mp hS))
  have key := Finset.sum_fiberwise_of_maps_to (s := s.powerset)
    (t := Finset.range (s.card + 1)) (g := Finset.card) hmem g
  simp only [Finset.powersetCard_eq_filter]
  exact key

/-- The sum over the singletons of a two-element set. -/
lemma sum_singletons {a b : ℕ} (hab : a ≠ b) (G : Finset ℕ → ℝ) :
    (∑ x ∈ ({a, b} : Finset ℕ), G ({x} : Finset ℕ)) = G {a} + G {b} := by
  rw [show ({a, b} : Finset ℕ) = insert a (insert b (∅ : Finset ℕ)) from rfl,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false]
      exact hab),
    Finset.sum_insert (Finset.notMem_empty b), Finset.sum_empty, add_zero]

/-- The map-form of `sum_singletons`. -/
lemma sum_singletons_emb {a b : ℕ} (hab : a ≠ b) (f : ℕ ↪ Finset ℕ)
    (hf : ∀ x : ℕ, f x = ({x} : Finset ℕ)) (G : Finset ℕ → ℝ) :
    (∑ x ∈ ({a, b} : Finset ℕ), G (f x)) = G {a} + G {b} := by
  rw [show (∑ x ∈ ({a, b} : Finset ℕ), G (f x))
      = ∑ x ∈ ({a, b} : Finset ℕ), G ({x} : Finset ℕ) from
    Finset.sum_congr rfl (fun x _ => by rw [hf x])]
  exact sum_singletons hab G

/-- **The `(U,V)`-sum for a two-element slot set**, in explicit form. -/
lemma sum_pair_powersetCard {a b : ℕ} (hab : a ≠ b) (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ U ∈ ({a, b} : Finset ℕ).powerset,
        ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (U.card + 1), F U V)
      = F ∅ {a} + F ∅ {b} + F {a} {a, b} + F {b} {a, b} := by
  have hcardtwo : ({a, b} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hab),
      Finset.card_singleton]
  have hcardone : ∀ x : ℕ, ({x} : Finset ℕ).card = 1 := fun x => Finset.card_singleton x
  have hsum2 : ({a, b} : Finset ℕ).powersetCard 2 = {({a, b} : Finset ℕ)} := by
    rw [← hcardtwo]; exact Finset.powersetCard_self _
  have hset1 : ({a, b} : Finset ℕ).powersetCard 1
      = ({a, b} : Finset ℕ).image (fun x => ({x} : Finset ℕ)) := by
    rw [Finset.powersetCard_one, Finset.map_eq_image]
    rfl
  -- the `U = ∅` term
  have h01 : (∑ U ∈ ({a, b} : Finset ℕ).powersetCard 0,
      ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (U.card + 1), F U V)
      = F ∅ {a} + F ∅ {b} := by
    rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.card_empty, zero_add, hset1,
      Finset.sum_image (by intro x _ y _ hxy; exact Finset.singleton_injective hxy)]
    exact sum_singletons hab (fun S => F ∅ S)
  -- the `U` of cardinality one
  have h2 : (∑ U ∈ ({a, b} : Finset ℕ).powersetCard 1,
      ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (U.card + 1), F U V)
      = F {a} {a, b} + F {b} {a, b} := by
    rw [hset1, Finset.sum_image (by
      intro x _ y _ hxy; exact Finset.singleton_injective hxy)]
    rw [sum_singletons hab (fun S =>
      ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (S.card + 1), F S V)]
    congr 1 <;>
      rw [Finset.card_singleton, show (1 : ℕ) + 1 = 2 from rfl, hsum2, Finset.sum_singleton]
  -- the `U = {a,b}` term vanishes
  have h3 : (∑ U ∈ ({a, b} : Finset ℕ).powersetCard 2,
      ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (U.card + 1), F U V) = 0 := by
    rw [hsum2, Finset.sum_singleton, hcardtwo,
      Finset.powersetCard_eq_empty.mpr (by rw [hcardtwo]; norm_num)]
    simp
  rw [← sum_powersetCard_eq_sum_powerset_gen ({a, b} : Finset ℕ)
      (fun U => ∑ V ∈ ({a, b} : Finset ℕ).powersetCard (U.card + 1), F U V), hcardtwo]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [h3, h2, h01]
  ring

/-- **Evaluation on a two-slot weight.** -/
lemma bandFun_pair {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (i : Fin n), i ≠ a → i ≠ b → ∀ (x : Submission.BoseGases.X n)
      (z : EuclideanSpace ℝ (Fin 3)), W (Function.update x i z) = W x)
    (hWi : IntegrableOn W (abox n ℓ)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFun ℓ n W Φ
      = (∫ x in abox n ℓ, aP ℓ a (aP ℓ b Φ) x * W x * aQ ℓ a (aP ℓ b Φ) x)
        + (∫ x in abox n ℓ, aP ℓ a (aP ℓ b Φ) x * W x * aP ℓ a (aQ ℓ b Φ) x)
        + (∫ x in abox n ℓ, aP ℓ a (aQ ℓ b Φ) x * W x * aQ ℓ a (aQ ℓ b Φ) x)
        + (∫ x in abox n ℓ, aQ ℓ a (aP ℓ b Φ) x * W x * aQ ℓ a (aQ ℓ b Φ) x) := by
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hA : ({a.val, b.val} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_insert.mp hk with h | h
    · rw [h]; exact Finset.mem_range.mpr a.isLt
    · rw [Finset.mem_singleton.mp h]; exact Finset.mem_range.mpr b.isLt
  have h := band_sum_eq_sum_projOn (A := {a.val, b.val}) hℓ hA hWi
    (fun i hi hiA x z =>
      hWin ⟨i, hi⟩
        (fun hcon => hiA (Finset.mem_insert.mpr (Or.inl (by
          have := congrArg Fin.val hcon; simpa using this))))
        (fun hcon => hiA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by
          have := congrArg Fin.val hcon; simpa using this))))) x z) hΦ
  rw [bandFun, h]
  rw [show (∑ U ∈ ({a.val, b.val} : Finset ℕ).powerset,
        ∑ V ∈ ({a.val, b.val} : Finset ℕ).powerset.filter (fun V => V.card = U.card + 1),
          ∫ x in abox n ℓ, projOn ℓ {a.val, b.val} U Φ x * W x
            * projOn ℓ {a.val, b.val} V Φ x)
      = ∑ U ∈ ({a.val, b.val} : Finset ℕ).powerset,
        ∑ V ∈ ({a.val, b.val} : Finset ℕ).powersetCard (U.card + 1),
          ∫ x in abox n ℓ, projOn ℓ {a.val, b.val} U Φ x * W x
            * projOn ℓ {a.val, b.val} V Φ x from
    Finset.sum_congr rfl (fun U _ => by rw [← Finset.powersetCard_eq_filter])]
  rw [sum_pair_powersetCard habv (fun U V => ∫ x in abox n ℓ,
    projOn ℓ {a.val, b.val} U Φ x * W x * projOn ℓ {a.val, b.val} V Φ x)]
  have h1 : projOn ℓ {a.val, b.val} ∅ Φ = aP ℓ a (aP ℓ b Φ) := by
    rw [projOn_pair hℓ a b hab ∅ hΦ.continuous]; simp
  have h2 : projOn ℓ {a.val, b.val} {a.val} Φ = aQ ℓ a (aP ℓ b Φ) := by
    rw [projOn_pair hℓ a b hab {a.val} hΦ.continuous]
    simp [habv, Ne.symm habv]
  have h3 : projOn ℓ {a.val, b.val} {b.val} Φ = aP ℓ a (aQ ℓ b Φ) := by
    rw [projOn_pair hℓ a b hab {b.val} hΦ.continuous]
    simp [habv, Ne.symm habv]
  have h4 : projOn ℓ {a.val, b.val} {a.val, b.val} Φ = aQ ℓ a (aQ ℓ b Φ) := by
    rw [projOn_pair hℓ a b hab {a.val, b.val} hΦ.continuous]
    simp
  rw [h1, h2, h3, h4]
  ring


end

end Work.BoseFixB2.DvApriori
