import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.KernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.near_set_finite`

The *near set* of the honest lattice row,

`{m : ℤ³ \ {0} | ℓ‖vecZ m‖ < 2R + √6}`,

is finite, with the absolute cardinality bound `1000`.  The whole content is the
elementary observation that `ℓ ≥ 1`, `R ≤ ℓ` force

`ℓ‖vecZ m‖ < 2R + √6  ⟹  ‖vecZ m‖ < 2 + √6 < 5`,

hence every coordinate of `m` lies in `[-4,4]`: the near set sits inside the
`9³ = 729` functions `Fin 3 → {−4,…,4} ⊂ ℤ`, so `card ≤ 729 ≤ 1000`.

The file proves this in three pieces, each reusable on its own:

* `norm_vecZ_lt_five` — the analytic core: the numerical bound `‖vecZ m‖ < 5`;
* `lattice_coord_bound` — its coordinate-wise consequence `|m i| ≤ 4`;
* `lattice_box_lift` — the (explicit) surjection `Fin 3 → Fin 9 ↠ {|m i| ≤ 4}`,
  `g ↦ (fun i => (g i : ℤ) - 4)`, used to build the finite superset.
-/

namespace Work.BoseRowsFS

open scoped BigOperators

/-- **The analytic core of `near_set_finite`.**  If `ℓ ≥ 1` and `R ≤ ℓ`, then any lattice
vector `m` in the near set `ℓ‖vecZ m‖ < 2R + √6` already satisfies `‖vecZ m‖ < 5`
(indeed `‖vecZ m‖ < 2 + √6 < 5`). -/
lemma norm_vecZ_lt_five {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hRℓ : R ≤ ℓ) {m : Fin 3 → ℤ}
    (h : ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6) : ‖vecZ m‖ < 5 := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hstep : ℓ * ‖vecZ m‖ < 2 * ℓ + Real.sqrt 6 := by linarith
  have h2 : ‖vecZ m‖ < (2 * ℓ + Real.sqrt 6) / ℓ := by
    rw [lt_div_iff₀ hℓpos]; linarith
  have h3 : (2 * ℓ + Real.sqrt 6) / ℓ = 2 + Real.sqrt 6 / ℓ := by field_simp
  have h4 : Real.sqrt 6 / ℓ ≤ Real.sqrt 6 := by
    rw [div_le_iff₀ hℓpos]; nlinarith [Real.sqrt_nonneg 6]
  rw [h3] at h2
  have h6 : Real.sqrt 6 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- **Every coordinate of a near lattice vector lies in `[-4,4]`.**  This is
`norm_vecZ_lt_five` together with the fact that the `i`-th coordinate of `vecZ m` is
dominated by `‖vecZ m‖` (since `‖vecZ m‖² = ∑ j, (m j)²`). -/
lemma lattice_coord_bound {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hRℓ : R ≤ ℓ) {m : Fin 3 → ℤ}
    (h : ℓ * ‖vecZ m‖ < 2 * R + Real.sqrt 6) (i : Fin 3) :
    -(4 : ℤ) ≤ m i ∧ m i ≤ 4 := by
  have hnorm : ‖vecZ m‖ < 5 := norm_vecZ_lt_five hℓ hRℓ h
  have hle : |(((m i : ℤ)) : ℝ)| ≤ ‖vecZ m‖ := by
    have hsq : (((m i : ℤ)) : ℝ) ^ 2 ≤ ∑ j, (((m j : ℤ)) : ℝ) ^ 2 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 3 => (((m j : ℤ)) : ℝ) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [← norm_vecZ_sq m] at hsq
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hlt : |(((m i : ℤ)) : ℝ)| < 5 := lt_of_le_of_lt hle hnorm
  have hcast : |(((m i : ℤ)) : ℝ)| = (((|m i| : ℤ)) : ℝ) := by rw [Int.cast_abs]
  rw [hcast] at hlt
  have hlt' : (|m i| : ℤ) < 5 := by exact_mod_cast hlt
  have h4' : |m i| ≤ 4 := (Int.lt_add_one_iff.mp (by norm_num at hlt' ⊢; omega))
  have := abs_le.mp h4'
  omega

/-- **The coordinate box of the lattice is a surjective image of `Fin 3 → Fin 9`**:
given `m` with every coordinate in `[-4,4]`, the function
`g i = ⟨(m i + 4).toNat, _⟩ : Fin 9` reconstructs `m` through `g ↦ (fun i => (g i : ℤ) - 4)`. -/
lemma lattice_box_lift {m : Fin 3 → ℤ} (hm : ∀ i, -(4 : ℤ) ≤ m i ∧ m i ≤ 4) :
    ∃ g : Fin 3 → Fin 9, (fun i => (g i : ℤ) - 4) = m := by
  refine ⟨fun i => ⟨Int.toNat (m i + 4), by have := (hm i).1; have := (hm i).2; omega⟩, ?_⟩
  funext i
  simp only
  have : ((Int.toNat (m i + 4) : ℕ) : ℤ) = m i + 4 :=
    Int.toNat_of_nonneg (by have := (hm i).1; omega)
  omega

/-- **The near set of the lattice row is finite, with `card ≤ 1000`.**  The witnessing finset
is the image of the finite set of indices `g : Fin 3 → Fin 9` whose image
`(fun i => (g i : ℤ) - 4)` is nonzero and near; by `lattice_coord_bound` every near `m` arises
this way, and the image has at most `9³ = 729 ≤ 1000` elements. -/
theorem near_set_finite {ℓ R : ℝ} (hℓ : 1 ≤ ℓ) (hRℓ : R ≤ ℓ) :
    ∃ S : Finset (Fin 3 → ℤ),
      (∀ m ∈ S, m ≠ 0 ∧ ℓ * ‖Work.BoseRowsFS.vecZ m‖ < 2 * R + Real.sqrt 6) ∧
      (∀ m : Fin 3 → ℤ, m ≠ 0 → ℓ * ‖Work.BoseRowsFS.vecZ m‖ < 2 * R + Real.sqrt 6 → m ∈ S) ∧
      S.card ≤ 1000 := by
  classical
  let f : (Fin 3 → Fin 9) → (Fin 3 → ℤ) := fun g i => (g i : ℤ) - 4
  refine ⟨((Finset.univ : Finset (Fin 3 → Fin 9)).filter
      (fun g => f g ≠ 0 ∧ ℓ * ‖vecZ (f g)‖ < 2 * R + Real.sqrt 6)).image f, ?_, ?_, ?_⟩
  · intro m hm
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨g, hg, rfl⟩ := hm
    exact hg
  · intro m hm0 hcond
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨g, hg⟩ := lattice_box_lift (lattice_coord_bound hℓ hRℓ hcond)
    exact ⟨g, by rw [show f g = m from hg]; exact ⟨hm0, hcond⟩, hg⟩
  · calc (((Finset.univ : Finset (Fin 3 → Fin 9)).filter
          (fun g => f g ≠ 0 ∧ ℓ * ‖vecZ (f g)‖ < 2 * R + Real.sqrt 6)).image f).card
        ≤ ((Finset.univ : Finset (Fin 3 → Fin 9)).filter
            (fun g => f g ≠ 0 ∧ ℓ * ‖vecZ (f g)‖ < 2 * R + Real.sqrt 6)).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin 3 → Fin 9)).card := Finset.card_filter_le _ _
      _ = 729 := by simp
      _ ≤ 1000 := by norm_num

end Work.BoseRowsFS
