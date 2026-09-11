import Submission.Gerzon

open EquiangularLinesFixedAngle
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

/-! Bridge between the set-based `N α d = ⨆ E, ncard E.carrier` and indexed configurations. -/

/-- Enumerate a finite carrier of an equiangular configuration. -/
lemma exists_enumerate (α : ℝ) {d : ℕ} (E : EquiangularLines α d) (hfin : E.carrier.Finite) :
    ∃ (m : ℕ) (v : Fin m → EuclideanSpace ℝ (Fin d)),
      m = E.carrier.ncard ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ ⦃i j : Fin m⦄, i ≠ j → |⟪v i, v j⟫| = α) := by
  classical
  rcases hfin.fin_param with ⟨n, f, hfinj, hrange⟩
  refine ⟨n, f, ?_, ?_, ?_⟩
  · have huniv : (Set.univ : Set (Fin n)).ncard = n := by
      rw [Set.ncard_univ]
      exact Nat.card_fin n
    calc
      n = (Set.univ : Set (Fin n)).ncard := huniv.symm
      _ = (f '' Set.univ).ncard := (Set.InjOn.ncard_image hfinj.injOn).symm
      _ = (Set.range f).ncard := by rw [Set.image_univ]
      _ = E.carrier.ncard := by rw [hrange]
  · intro i
    have hx : f i ∈ E.carrier := by
      rw [← hrange]
      exact Set.mem_range_self i
    exact E.norm (f i) hx
  · intro i j hij
    have hx : f i ∈ E.carrier := by
      rw [← hrange]
      exact Set.mem_range_self i
    have hy : f j ∈ E.carrier := by
      rw [← hrange]
      exact Set.mem_range_self j
    exact E.angle hx hy (hfinj.ne hij)

lemma ncard_zero_of_infinite {α : Type*} (s : Set α) (hs : ¬ s.Finite) : s.ncard = 0 := by
  classical
  have hinf : s.Infinite := by
    change ¬ s.Finite
    exact hs
  dsimp [Set.ncard]
  rw [Set.Infinite.encard_eq hinf]
  exact ENat.toNat_top

/-- Every equiangular configuration in `𝔼^d` has at most `d²` lines. -/
lemma ncard_bound {α : ℝ} {d : ℕ} (E : EquiangularLines α d) (hα0 : 0 < α) (hα1 : α < 1) :
    E.carrier.ncard ≤ d ^ 2 := by
  classical
  by_cases hfin : E.carrier.Finite
  · rcases exists_enumerate α E hfin with ⟨m, v, hm, hvnorm, hvangle⟩
    have hle : m ≤ d ^ 2 := card_le_sq v hα0 hα1 hvnorm hvangle
    rwa [hm] at hle
  · have hz : E.carrier.ncard = 0 := ncard_zero_of_infinite E.carrier hfin
    rw [hz]
    exact Nat.zero_le (d ^ 2)

/-- `N` is bounded by any bound that holds for all configurations. -/
lemma N_le_of_bound {α : ℝ} {d X : ℕ} (hα0 : 0 < α) (hα1 : α < 1)
    (hX : ∀ (E : EquiangularLines α d), E.carrier.ncard ≤ X) : N α d ≤ X := by
  classical
  change sSup (Set.range (fun E : EquiangularLines α d => E.carrier.ncard)) ≤ X
  by_cases hne : (Set.range (fun E : EquiangularLines α d => E.carrier.ncard)).Nonempty
  · exact csSup_le hne (by
      intro b hb
      rcases hb with ⟨E, rfl⟩
      exact hX E)
  · have hr : (Set.range (fun E : EquiangularLines α d => E.carrier.ncard)) = ∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp hne
    rw [hr, csSup_empty]
    exact Nat.zero_le X

/-- Upper bound for `N` from a bound on all indexed families. -/
lemma N_le_of_card_le {α : ℝ} {d : ℕ} {X : ℕ} (hα0 : 0 < α) (hα1 : α < 1)
    (hX : ∀ {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖v i‖ = 1) →
      (∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) → n ≤ X) :
    N α d ≤ X := by
  classical
  apply N_le_of_bound hα0 hα1
  intro E
  by_cases hfin : E.carrier.Finite
  · rcases exists_enumerate α E hfin with ⟨m, v, hm, hvnorm, hvangle⟩
    have hle : m ≤ X := hX v hvnorm hvangle
    rwa [hm] at hle
  · have hz : E.carrier.ncard = 0 := ncard_zero_of_infinite E.carrier hfin
    rw [hz]
    exact Nat.zero_le X

/-- A configuration of `n` lines gives `n ≤ N α d`. -/
lemma le_N_of_hasLines {α : ℝ} {n d : ℕ} (hα0 : 0 < α) (hα1 : α < 1)
    (h : HasLines α n d) : n ≤ N α d := by
  classical
  rcases h with ⟨v, hvnorm, hvangle⟩
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have hpair := hvangle hne
    have hself : |⟪v i, v j⟫| = 1 := by
      rw [hij, real_inner_self_eq_norm_sq, hvnorm j]
      norm_num
    linarith
  let E : EquiangularLines α d :=
    { carrier := Set.range v
      norm := by
        intro x hx
        rcases hx with ⟨i, rfl⟩
        exact hvnorm i
      angle := by
        intro x hx y hy hxy
        rcases hx with ⟨i, rfl⟩
        rcases hy with ⟨j, rfl⟩
        have : i ≠ j := by
          intro hij
          apply hxy
          rw [hij]
        exact hvangle this }
  change n ≤ sSup (Set.range (fun E : EquiangularLines α d => E.carrier.ncard))
  have hncard : E.carrier.ncard = n := by
    change (Set.range v).ncard = n
    rw [← Set.image_univ]
    rw [Set.InjOn.ncard_image hinj.injOn]
    simp
  apply le_csSup
  · exact ⟨d ^ 2, by intro b hb; rcases hb with ⟨E, rfl⟩; exact ncard_bound E hα0 hα1⟩
  · exact ⟨E, hncard⟩

/-- Gerzon-type bound at the level of `N`: `N α d ≤ d²`. -/
lemma N_le_sq {α : ℝ} {d : ℕ} (hα0 : 0 < α) (hα1 : α < 1) : N α d ≤ d ^ 2 := by
  classical
  exact N_le_of_bound hα0 hα1 (fun E => ncard_bound E hα0 hα1)

end Submission
