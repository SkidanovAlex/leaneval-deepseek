import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilE7.exists_continuous_selection
import Submission.Work.WilE7.ereal_between_convex

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign

/-! ## Cylindrical cells are contractible

A cell of the frozen decomposition `WilkiesDesign.IsCell` is `ℝ⁰`, a graph over a cell, or a
band between two continuous `EReal`-valued boundary functions over a cell.  Each of the three
is contractible:

* `ℝ⁰` is a point;
* the graph of a function continuous on the base `C` is the image of `C` under the continuous
  map `x ↦ Fin.snoc x (f x)`, so a contraction of `C` transports to one of the graph;
* a band `{(x,y) | x ∈ C, a x < y < b x}` contracts by first sliding the vertical coordinate
  onto a continuous section `m` of the interval family (which exists by
  `Work.WilE7.exists_continuous_selection`, an explicit "midpoint" construction using the
  order-homeomorphism `EReal ≅ [-1,1]`), and then contracting the base.

The two constructors are isolated in the lemmas `hasContraction_graph` and
`hasContraction_band`, and the induction is closed by `hasContraction_of_isCell`. -/

/-- Data of a contraction of `A ⊆ ℝⁿ` to a point of itself: a base point `c₀ ∈ A` and a
homotopy `K : ℝⁿ × ℝ → ℝⁿ` that is continuous on `A × [0,1]`, sends `(·,0)` to the constant
`c₀`, sends `(·,1)` to the identity, and stays inside `A`. -/
def HasContraction {n : ℕ} (A : Set (Fin n → ℝ)) : Prop :=
  ∃ (c₀ : Fin n → ℝ) (K : (Fin n → ℝ) × ℝ → (Fin n → ℝ)),
    c₀ ∈ A ∧ ContinuousOn K (A ×ˢ Set.Icc (0 : ℝ) 1) ∧ (∀ x ∈ A, K (x, 0) = c₀) ∧
      (∀ x ∈ A, K (x, 1) = x) ∧
      (∀ x ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, K (x, t) ∈ A)

/-- A graph over a contractible set is contractible. -/
theorem hasContraction_graph {n : ℕ} {C : Set (Fin n → ℝ)} (hC : HasContraction C)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f C) :
    HasContraction {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} := by
  rcases hC with ⟨c₀, K, hc₀, hKcont, hK0, hK1, hKmem⟩
  have hΦ : ContinuousOn (fun u : Fin n → ℝ => (Fin.snoc u (f u) : Fin (n+1) → ℝ)) C :=
    ContinuousOn.finSnoc (X := fun _ => ℝ) continuousOn_id hf
  refine ⟨(Fin.snoc c₀ (f c₀) : Fin (n+1) → ℝ), fun p : (Fin (n+1) → ℝ) × ℝ =>
      Fin.snoc (K (Fin.init p.1, p.2)) (f (K (Fin.init p.1, p.2))), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [Fin.init_snoc]; exact hc₀,
           by rw [Fin.snoc_last, Fin.init_snoc]⟩
  · have hmap1 : Set.MapsTo (fun p : (Fin (n+1) → ℝ) × ℝ => (Fin.init p.1, p.2))
        ({z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} ×ˢ
          Set.Icc (0:ℝ) 1) (C ×ˢ Set.Icc (0:ℝ) 1) := fun p hp => ⟨hp.1.1, hp.2⟩
    have hmap2 : Set.MapsTo (fun p : (Fin (n+1) → ℝ) × ℝ => K (Fin.init p.1, p.2))
        ({z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} ×ˢ
          Set.Icc (0:ℝ) 1) C := fun p hp => hKmem (Fin.init p.1) hp.1.1 p.2 hp.2
    exact hΦ.comp (hKcont.comp (by fun_prop) hmap1) hmap2
  · intro x hx
    show Fin.snoc (K (Fin.init x, 0)) (f (K (Fin.init x, 0))) =
      (Fin.snoc c₀ (f c₀) : Fin (n+1) → ℝ)
    rw [hK0 (Fin.init x) hx.1]
  · intro x hx
    show Fin.snoc (K (Fin.init x, 1)) (f (K (Fin.init x, 1))) = x
    rw [hK1 (Fin.init x) hx.1, ← hx.2]
    exact Fin.snoc_init_self x
  · intro x hx t ht
    refine ⟨?_, ?_⟩
    · simp only [Fin.init_snoc]
      exact hKmem (Fin.init x) hx.1 t ht
    · simp only [Fin.snoc_last, Fin.init_snoc]

/-- A band between two continuous `EReal`-valued boundaries over a contractible set is
contractible.  The vertical coordinate is first slid onto a continuous section `m` of the
interval family `(a x, b x)`, and the base is then contracted while staying on the section. -/
theorem hasContraction_band {n : ℕ} {C : Set (Fin n → ℝ)} (hC : HasContraction C)
    (a b : (Fin n → ℝ) → EReal) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    HasContraction {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  rcases hC with ⟨c₀, K, hc₀, hKcont, hK0, hK1, hKmem⟩
  rcases exists_continuous_selection ha hb hab with ⟨m, hmcont, hmmem⟩
  set A : Set (Fin (n+1) → ℝ) := {z | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} with hAdef
  set U : Set ((Fin (n+1) → ℝ) × ℝ) := A ×ˢ Set.Icc (0:ℝ) 1 with hUdef
  have hmemA : ∀ z : Fin (n+1) → ℝ, z ∈ A ↔ (Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)) := by
    intro z; rw [hAdef]; exact Iff.rfl
  have hint : ∀ t ∈ Set.Icc (0:ℝ) 1, min (2 * t) 1 ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨le_min (by linarith [ht.1]) zero_le_one, min_le_right _ _⟩
  have hX : ContinuousOn (fun p : (Fin (n+1) → ℝ) × ℝ => K (Fin.init p.1, min (2 * p.2) 1)) U := by
    refine hKcont.comp (by fun_prop) ?_
    rintro ⟨z, t⟩ hp
    have hz : z ∈ A := hp.1
    exact ⟨((hmemA z).mp hz).1, hint t hp.2⟩
  have hmX : ContinuousOn (fun p : (Fin (n+1) → ℝ) × ℝ =>
      m (K (Fin.init p.1, min (2 * p.2) 1))) U := by
    refine hmcont.comp hX ?_
    rintro ⟨z, t⟩ hp
    have hz : z ∈ A := hp.1
    exact hKmem (Fin.init z) ((hmemA z).mp hz).1 (min (2*t) 1) (hint t hp.2)
  have hrest : ContinuousOn (fun p : (Fin (n+1) → ℝ) × ℝ =>
      (1 - max (2 * p.2 - 1) 0) * m (K (Fin.init p.1, min (2 * p.2) 1)) +
        max (2 * p.2 - 1) 0 * (p.1 (Fin.last n))) U := by
    have h1 : ContinuousOn (fun p : (Fin (n+1) → ℝ) × ℝ => (1 - max (2 * p.2 - 1) 0)) U := by
      fun_prop
    have h2 : ContinuousOn (fun p : (Fin (n+1) → ℝ) × ℝ => max (2 * p.2 - 1) 0) U := by fun_prop
    have h3 : ContinuousOn (fun p : (Fin (n+1) → ℝ) × ℝ => p.1 (Fin.last n)) U := by fun_prop
    exact (h1.mul hmX).add (h2.mul h3)
  refine ⟨(Fin.snoc c₀ (m c₀) : Fin (n+1) → ℝ), fun p : (Fin (n+1) → ℝ) × ℝ =>
      Fin.snoc (K (Fin.init p.1, min (2 * p.2) 1))
        ((1 - max (2 * p.2 - 1) 0) * m (K (Fin.init p.1, min (2 * p.2) 1)) +
          max (2 * p.2 - 1) 0 * (p.1 (Fin.last n))), ?_, ?_, ?_, ?_, ?_⟩
  · refine (hmemA _).mpr ⟨?_, ?_, ?_⟩
    · rw [Fin.init_snoc]; exact hc₀
    · rw [Fin.init_snoc, Fin.snoc_last]; exact (hmmem c₀ hc₀).1
    · rw [Fin.init_snoc, Fin.snoc_last]; exact (hmmem c₀ hc₀).2
  · exact ContinuousOn.finSnoc (X := fun _ => ℝ) hX hrest
  · intro x hx
    have hxC : Fin.init x ∈ C := ((hmemA x).mp hx).1
    have hE : (1 - max (2 * (0:ℝ) - 1) 0) * m c₀ + max (2 * (0:ℝ) - 1) 0 * (x (Fin.last n))
        = m c₀ := by norm_num
    show Fin.snoc (K (Fin.init x, min (2 * (0:ℝ)) 1))
      ((1 - max (2 * (0:ℝ) - 1) 0) * m (K (Fin.init x, min (2 * (0:ℝ)) 1)) +
        max (2 * (0:ℝ) - 1) 0 * (x (Fin.last n))) = (Fin.snoc c₀ (m c₀) : Fin (n+1) → ℝ)
    rw [show min (2 * (0:ℝ)) 1 = 0 from by norm_num, hK0 (Fin.init x) hxC, hE]
  · intro x hx
    have hxC : Fin.init x ∈ C := ((hmemA x).mp hx).1
    have hE : (1 - max (2 * (1:ℝ) - 1) 0) * m (Fin.init x) +
        max (2 * (1:ℝ) - 1) 0 * (x (Fin.last n)) = x (Fin.last n) := by norm_num
    show Fin.snoc (K (Fin.init x, min (2 * (1:ℝ)) 1))
      ((1 - max (2 * (1:ℝ) - 1) 0) * m (K (Fin.init x, min (2 * (1:ℝ)) 1)) +
        max (2 * (1:ℝ) - 1) 0 * (x (Fin.last n))) = x
    rw [show min (2 * (1:ℝ)) 1 = 1 from by norm_num, hK1 (Fin.init x) hxC, hE]
    exact Fin.snoc_init_self x
  · intro x hx t ht
    obtain ⟨hxC, hxa, hxb⟩ := (hmemA x).mp hx
    have hKu : K (Fin.init x, min (2*t) 1) ∈ C :=
      hKmem (Fin.init x) hxC (min (2*t) 1) (hint t ht)
    refine (hmemA _).mpr ?_
    simp only [Fin.init_snoc, Fin.snoc_last]
    refine ⟨hKu, ?_⟩
    by_cases ht2 : t ≤ 1/2
    · have hv0 : max (2 * t - 1) 0 = 0 := max_eq_right (by linarith [ht2])
      have hY : (1 - max (2 * t - 1) 0) * m (K (Fin.init x, min (2*t) 1)) +
          max (2*t - 1) 0 * (x (Fin.last n)) = m (K (Fin.init x, min (2*t) 1)) := by
        rw [hv0]; ring
      rw [hY]
      exact ⟨(hmmem (K (Fin.init x, min (2*t) 1)) hKu).1,
             (hmmem (K (Fin.init x, min (2*t) 1)) hKu).2⟩
    · have ht2' : (1:ℝ)/2 < t := not_le.mp ht2
      have hu1 : min (2 * t) 1 = 1 := min_eq_right (by linarith [ht2'])
      have hKx : K (Fin.init x, min (2*t) 1) = Fin.init x := by
        rw [hu1]; exact hK1 (Fin.init x) hxC
      rw [hKx]
      exact ereal_between_convex (s := max (2*t - 1) 0) (r₁ := m (Fin.init x))
        (r₂ := x (Fin.last n)) ⟨(hmmem (Fin.init x) hxC).1, (hmmem (Fin.init x) hxC).2⟩
        ⟨hxa, hxb⟩ (le_max_right _ _) (max_le (by linarith [ht.2]) zero_le_one)

/-- Every cylindrical cell is contractible. -/
theorem hasContraction_of_isCell : ∀ {n : ℕ} {A : Set (Fin n → ℝ)},
    WilkiesDesign.IsCell n A → HasContraction A := by
  intro n A hA
  induction hA with
  | zero =>
    refine ⟨Fin.elim0, fun p => p.1, Set.mem_univ _, ?_, ?_, ?_, ?_⟩
    · exact continuous_fst.continuousOn.mono (Set.subset_univ _)
    · intro x hx; exact Subsingleton.elim x Fin.elim0
    · intro x hx; rfl
    · intro x hx t ht; exact Set.mem_univ _
  | graph hC f hf ih => exact hasContraction_graph ih f hf
  | band hC a b ha hb hab ih => exact hasContraction_band ih a b ha hb hab

theorem isCellContractible {n : ℕ} {A : Set (Fin n → ℝ)} (hA : WilkiesDesign.IsCell n A) :
    ∃ (c₀ : Fin n → ℝ) (K : (Fin n → ℝ) × ℝ → (Fin n → ℝ)),
      c₀ ∈ A ∧ ContinuousOn K (A ×ˢ Set.Icc (0 : ℝ) 1) ∧ (∀ x ∈ A, K (x, 0) = c₀) ∧
        (∀ x ∈ A, K (x, 1) = x) ∧
        (∀ x ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, K (x, t) ∈ A) :=
  hasContraction_of_isCell hA

end Work.WilE7

