import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.FM.latStep_min

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP.Sig2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Realifying an integer linear combination of integer vectors. -/
lemma cast_TZ {R K : ℕ} (u : Fin R → ℤ) (v : Fin K → (Fin R → ℤ)) (c : ℤ × (Fin K → ℤ)) :
    (fun j => ((c.1 • u + ∑ i, c.2 i • v i) j : ℝ))
      = (c.1 : ℝ) • (fun j => (u j : ℝ)) + ∑ i, (c.2 i : ℝ) • (fun j => (v i j : ℝ)) := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  push_cast
  ring

/-- The standard basis vector, realified. -/
lemma single_cast {α : Type*} [DecidableEq α] (k : α) :
    (fun j => (((Pi.single k (1 : ℤ)) : α → ℤ) j : ℝ))
      = ((Pi.single k (1 : ℝ)) : α → ℝ) := by
  funext j
  by_cases h : j = k <;> simp [h]

/-- A `ℤ`-basis `(u, v)` of `ℤ^R` is also an `ℝ`-basis of `ℝ^R`: the realified family
`(u, v)` is `ℝ`-linearly independent. -/
lemma indep_of_bij {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (hbij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
      c.1 • u + ∑ i, c.2 i • v i)) :
    ∀ c : ℝ × (Fin (R - 1) → ℝ),
      c.1 • (fun j => (u j : ℝ)) + ∑ i, c.2 i • (fun j => (v i j : ℝ)) = 0 → c = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by omega⟩
  intro c hc
  let w : Fin (n + 1) → (Fin (n + 1) → ℝ) :=
    Fin.cons (fun j => (u j : ℝ)) (fun i => fun j => (v i j : ℝ))
  have hw0 : w 0 = (fun j => (u j : ℝ)) := Fin.cons_zero _ _
  have hws : ∀ i : Fin n, w i.succ = (fun j => (v i j : ℝ)) := fun i => Fin.cons_succ _ _ _
  have hmem : ∀ k : Fin (n + 1),
      (Pi.single k (1 : ℝ)) ∈ Submodule.span ℝ (Set.range w) := by
    intro k
    obtain ⟨c', hc'⟩ := hbij.2 (Pi.single k (1 : ℤ))
    have hc'' : c'.1 • u + ∑ i, c'.2 i • v i = Pi.single k (1 : ℤ) := hc'
    have h1 : Pi.single k (1 : ℝ)
        = (Fintype.linearCombination ℝ w)
            (Fin.cons (c'.1 : ℝ) (fun i : Fin n => (c'.2 i : ℝ)) : Fin (n + 1) → ℝ) := by
      rw [Fintype.linearCombination_apply, ← single_cast k, ← hc'', cast_TZ u v c']
      rw [Fin.sum_univ_succ]
      simp only [hw0, hws, Fin.cons_zero, Fin.cons_succ]
      rfl
    rw [h1, ← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ _
  have hstd : (⊤ : Submodule ℝ (Fin (n + 1) → ℝ)) ≤ Submodule.span ℝ (Set.range w) := by
    rw [← (Pi.basisFun ℝ (Fin (n + 1))).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    exact hmem k
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := le_antisymm le_top hstd
  have hlin : LinearMap.range (Fintype.linearCombination ℝ w) = ⊤ := by
    rw [Fintype.range_linearCombination]; exact hspan
  have hsurj : Function.Surjective (Fintype.linearCombination ℝ w) :=
    LinearMap.range_eq_top.mp hlin
  have hinj : Function.Injective (Fintype.linearCombination ℝ w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Fintype.linearCombination ℝ w) rfl).mpr hsurj
  let a : Fin (n + 1) → ℝ := Fin.cons c.1 c.2
  have ha0 : a = 0 := by
    apply hinj
    rw [map_zero, Fintype.linearCombination_apply]
    rw [Fin.sum_univ_succ]
    simp only [hw0, hws]
    exact hc
  refine Prod.ext ?_ ?_
  · have := congrFun ha0 0
    simpa [a] using this
  · funext i
    have := congrFun ha0 i.succ
    simpa [a] using this

theorem latMin_latStep {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (Φ : Work.HP.LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (hbij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
      c.1 • u + ∑ i, c.2 i • v i))
    (hu : ‖Φ (fun j => (u j : ℝ))‖ = Work.HP.latMin Φ 1) :
    ∀ j : ℕ, 1 ≤ j → Work.HP.latMin Φ (j + 1) ≤ 2 * Work.HP.latMin (Work.HP.FM.latStep Φ u v) j := by
  have hpos : 0 < latMin Φ 1 := by
    obtain ⟨u₀, hu₀ne, -, hu₀⟩ := lat_min_attained hR Φ hΦ
    rw [← hu₀, norm_pos_iff]
    intro h
    have h0 : (fun i => (u₀ i : ℝ)) = 0 := hΦ (by rw [h, map_zero])
    exact hu₀ne (funext fun i => by
      have h2 : ((u₀ i : ℤ) : ℝ) = 0 := congrFun h0 i
      exact_mod_cast h2)
  have hune : u ≠ 0 := by
    intro h
    have h1 : (fun j => (u j : ℝ)) = 0 := by funext j; simp [h]
    have h2 : ‖Φ (fun j => (u j : ℝ))‖ = 0 := by rw [h1, map_zero, norm_zero]
    rw [hu] at h2
    exact absurd h2 (ne_of_gt hpos)
  have huprim : IsPrim u :=
    minimal_is_prim hR Φ hΦ hune (fun t ht => by rw [hu]; exact Work.HP.FM.lsm_latMin_one_le Φ ht)
  have hindep := indep_of_bij hR u v hbij
  let D : Work.HP.FM.RecData R ι := ⟨Φ, u, v, hΦ, hune, huprim, hbij, hindep⟩
  intro j hj
  have hmain : latMin Φ (j + 1) / 2 ≤ latMin (Work.HP.FM.latStep Φ u v) j :=
    Work.HP.FM.latStep_min D hu hj
  linarith [hmain]

end Work.HP.Sig2
