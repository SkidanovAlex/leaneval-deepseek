import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.decouple_defs

namespace Work.BourgainPlan.IonescuWainger

open Finset

/-- The underlying set of an injective tuple `σ : Fin k → S` has exactly `k` elements. -/
theorem tupleSet_card_of_injective {α : Type*} [DecidableEq α] (S : Finset α) {k : ℕ}
    {σ : Fin k → S} (hσ : Function.Injective σ) : (tupleSet S σ).card = k := by
  rw [tupleSet, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
  intro j j' h
  exact hσ (Subtype.ext h)

/-- The colourings `c : S → Fin k` that invert an injective tuple `σ` (i.e. `c (σ j) = j` for all
`j`) are exactly the arbitrary colourings of the complement of the range of `σ`; there are
`k ^ (#S - k)` of them. -/
noncomputable def colorEquiv {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin k → S) (hσ : Function.Injective σ) :
    {c : S → Fin k // ∀ j, c (σ j) = j} ≃ (↥(S \ tupleSet S σ) → Fin k) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact
  { toFun := fun c => fun x => c.1 ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩
    invFun := fun h => ⟨fun s => if hs : (s : α) ∈ tupleSet S σ then Function.invFun σ s
        else h ⟨s, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩, by
      intro j
      simp only []
      split_ifs with hh
      · exact Function.leftInverse_invFun hσ j
      · exact absurd (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hh⟩
    left_inv := by
      intro c
      apply Subtype.ext
      funext s
      simp only []
      split_ifs with hs
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hs
        have hjs : σ j = s := Subtype.ext hj
        rw [show Function.invFun σ s = j from by rw [← hjs]; exact Function.leftInverse_invFun hσ j,
            show c.1 s = j from by rw [← hjs]; exact c.2 j]
      · rfl
    right_inv := by
      intro h
      funext x
      simp only []
      split_ifs with hx
      · exact absurd hx (Finset.mem_sdiff.mp x.2).2
      · exact congrArg h (Subtype.ext rfl) }

theorem card_colorings {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin k → S) (hσ : Function.Injective σ) :
    (Finset.univ.filter (fun c : S → Fin k => ∀ j, c (σ j) = j)).card = k ^ (S.card - k) := by
  classical
  rw [← Fintype.card_subtype (fun c : S → Fin k => ∀ j, c (σ j) = j)]
  rw [Fintype.card_congr (colorEquiv S k hk σ hσ)]
  rw [Fintype.card_fun]
  rw [Fintype.card_coe, Finset.card_sdiff_of_subset (tupleSet_subset S σ),
      tupleSet_card_of_injective S hσ, Fintype.card_fin]

/-- An injective map `Fin k → A` with `#A = k` (or rather: a tuple into `A` whose underlying set is
`A`) corresponds to an injective map into `A`; there are `k!` such. -/
noncomputable def fiberEquiv {α : Type*} [DecidableEq α] (S A : Finset α) (k : ℕ) (hAS : A ⊆ S)
    (hAcard : A.card = k) :
    {σ : Fin k → S // Function.Injective σ ∧ tupleSet S σ = A} ≃
    {e : Fin k → A // Function.Injective e} where
  toFun σ := ⟨fun j => ⟨(σ.1 j).1, by
      have h : (σ.1 j).1 ∈ tupleSet S σ.1 :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      rwa [σ.2.2] at h⟩,
    fun j j' h => σ.2.1 (Subtype.ext (congrArg (fun x : A => (x : α)) h))⟩
  invFun e := ⟨fun j => ⟨(e.1 j).1, hAS (e.1 j).2⟩, ⟨
    fun j j' h => e.2 (Subtype.ext (congrArg (fun x : S => (x : α)) h)), by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_image.mp ha with ⟨j, -, rfl⟩
        exact (e.1 j).2
      · intro ha
        have hcard : Fintype.card (Fin k) = Fintype.card A := by
          rw [Fintype.card_fin, Fintype.card_coe]
          exact hAcard.symm
        have hbij : Function.Bijective e.1 :=
          (Fintype.bijective_iff_injective_and_card e.1).2 ⟨e.2, hcard⟩
        obtain ⟨j, hj⟩ := hbij.2 ⟨a, ha⟩
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, congrArg (fun x : A => (x : α)) hj⟩⟩⟩
  left_inv := by
    intro σ
    apply Subtype.ext
    funext j
    exact Subtype.ext rfl
  right_inv := by
    intro e
    apply Subtype.ext
    funext j
    exact Subtype.ext rfl

/-- The number of injective tuples `σ : Fin k → S` whose underlying set is a fixed `k`-subset `A`
of `S` is `k!`. -/
theorem card_injective_fiber {α : Type*} [DecidableEq α] (S A : Finset α) (k : ℕ)
    (hAS : A ⊆ S) (hAcard : A.card = k) :
    ((Finset.univ : Finset (Fin k → S)).filter
      (fun σ => Function.Injective σ ∧ tupleSet S σ = A)).card = k.factorial := by
  classical
  rw [← Fintype.card_subtype (fun σ : Fin k → S => Function.Injective σ ∧ tupleSet S σ = A)]
  rw [Fintype.card_congr (fiberEquiv S A k hAS hAcard)]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) A)]
  rw [Fintype.card_embedding_eq]
  rw [Fintype.card_coe, hAcard, Fintype.card_fin]
  exact Nat.descFactorial_self k

/-- Summing over the injective tuples `σ : Fin k → S` and grouping by their underlying set: each
`k`-subset of `S` is the underlying set of exactly `k!` injective tuples. -/
theorem sum_injective_tuples {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ)
    (g : Finset α → ℂ) :
    (∑ σ ∈ (Finset.univ.filter (fun σ : Fin k → S => Function.Injective σ)), g (tupleSet S σ))
      = (k.factorial : ℂ) * ∑ A ∈ S.powerset.filter (fun A => A.card = k), g A := by
  classical
  have hmaps : ∀ σ ∈ Finset.univ.filter (fun σ : Fin k → S => Function.Injective σ),
      tupleSet S σ ∈ S.powerset.filter (fun A => A.card = k) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (tupleSet_subset S σ),
      tupleSet_card_of_injective S hσ.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ.filter (fun σ : Fin k → S => Function.Injective σ))
    (t := S.powerset.filter (fun A => A.card = k))
    (g := fun σ : Fin k → S => tupleSet S σ) (f := g) hmaps]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
  rw [card_injective_fiber S A k (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
      (Finset.mem_filter.mp hA).2]

/-- **Averaging over colourings.**  For a family `g` indexed by the `k`-element subsets of `S`, the
total weight of the `k`-subsets (`k! · k^{|S|}` times their sum) equals `k^k` times the sum over
the `k^{|S|}` colourings `c : S → Fin k` of the sum of `g` over the transversal tuples of `c`.
Indeed, a `k`-subset `A` is the underlying set of a transversal tuple of `c` exactly when `c`
restricted to `A` is a bijection onto `Fin k`, which happens for `k! · k^{|S|-k}` colourings. -/
theorem sum_powerset_card_eq_avg {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) (hk : 1 ≤ k)
    (g : Finset α → ℂ) :
    ((k.factorial * k ^ S.card : ℕ) : ℂ) *
        ∑ A ∈ S.powerset.filter (fun A => A.card = k), g A
      = (k ^ k : ℕ) * ∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, g (tupleSet S σ) := by
  classical
  have hdouble : (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, g (tupleSet S σ))
      = (k.factorial : ℂ) * ((k ^ (S.card - k) : ℕ) : ℂ)
        * ∑ A ∈ S.powerset.filter (fun A => A.card = k), g A := by
    have h0 : (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, g (tupleSet S σ))
        = ∑ c : S → Fin k, ∑ σ : Fin k → S,
            (if ∀ j, c (σ j) = j then g (tupleSet S σ) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [transversalTuples, Finset.sum_filter]
    rw [h0, Finset.sum_comm]
    have h1 : ∀ σ : Fin k → S,
        (∑ c : S → Fin k, (if ∀ j, c (σ j) = j then g (tupleSet S σ) else 0))
          = g (tupleSet S σ)
            * ((Finset.univ.filter (fun c : S → Fin k => ∀ j, c (σ j) = j)).card : ℂ) := by
      intro σ
      have hc : ∀ c : S → Fin k,
          (if (∀ j, c (σ j) = j) then g (tupleSet S σ) else 0)
            = g (tupleSet S σ) * (if (∀ j, c (σ j) = j) then (1 : ℂ) else 0) := by
        intro c
        by_cases h : ∀ j, c (σ j) = j <;> simp [h]
      rw [Finset.sum_congr rfl (fun c _ => hc c)]
      rw [← Finset.mul_sum]
      rw [Finset.sum_boole]
    rw [Finset.sum_congr rfl (fun σ _ => h1 σ)]
    have h2 : ∀ σ : Fin k → S,
        g (tupleSet S σ) * ((Finset.univ.filter (fun c : S → Fin k => ∀ j, c (σ j) = j)).card : ℂ)
          = (if Function.Injective σ then g (tupleSet S σ) * ((k ^ (S.card - k) : ℕ) : ℂ)
              else 0) := by
      intro σ
      by_cases hσ : Function.Injective σ
      · rw [if_pos hσ, card_colorings S k hk σ hσ]
      · rw [if_neg hσ]
        have hempty : (Finset.univ.filter (fun c : S → Fin k => ∀ j, c (σ j) = j)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro c _ hc
          obtain ⟨j, j', hjj, hne⟩ := Function.not_injective_iff.mp hσ
          exact hne (by rw [← hc j, hjj, hc j'])
        rw [hempty]
        simp
    rw [Finset.sum_congr rfl (fun σ _ => h2 σ), ← Finset.sum_filter]
    rw [← Finset.sum_mul, sum_injective_tuples S k g]
    ring
  rw [hdouble]
  by_cases hks : k ≤ S.card
  · have hcoef : ((k.factorial * k ^ S.card : ℕ) : ℂ)
        = (k ^ k : ℕ) * ((k.factorial : ℂ) * ((k ^ (S.card - k) : ℕ) : ℂ)) := by
      have h1 : k ^ S.card = k ^ k * k ^ (S.card - k) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hks]
      rw [show k.factorial * k ^ S.card = k ^ k * (k.factorial * k ^ (S.card - k)) from by
        rw [h1]; ring]
      push_cast
      ring
    rw [hcoef]
    ring
  · have hTe : S.powerset.filter (fun A => A.card = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro A hA hc
      have hle : A.card ≤ S.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
      omega
    rw [hTe, Finset.sum_empty]
    simp

end Work.BourgainPlan.IonescuWainger
