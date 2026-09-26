import Mathlib
import Submission.Work.PinchCounted.TraceCover
import Submission.Work.CoreTopology.IntersectionNumberStandard

/-!
# The trace of a plane normal to the axis of the standard torus is a family of longitude circles

The standard torus of revolution `Work.CoreTopology.standard` (major radius `2`, minor radius `1`)
has parametrisation `torusMap θ φ = ((2 + cos φ) cos θ, (2 + cos φ) sin θ, sin φ)`, whose third
coordinate is `sin φ`.  Hence the trace of a horizontal plane `{z = v}` in the torus is a union of
*longitude* circles `{φ = const}`, one for each solution `φ` of `sin φ = v` — at most two circles,
and exactly one when `v = ±1`.

`exists_traceCircleFamily_z` packages this: for any real `v` there is a finite family of pairwise
disjoint simple closed curves on the standard torus, each inessential or meeting the standard
`(p,q)`-curve in at least `min p q` points (a longitude circle meets it in exactly `q ≥ min p q`
points, `Work.CoreTopology.encard_longitude_inter_standardCurve`), whose union covers the trace
`{z = v} ∩ F`.  This is the covering hypothesis of the "counted" route to the slice inessentiality
(`Work.PinchCounted.not_containsEssentialLoop_sliceRegion_of_traceCircles`), used in particular at
the axis-normal cutting planes of `Submission.Work.PinchCounted.AxisPlane`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

/-- The torus parametrisation is `2π`-periodic in the meridian variable, also by integer multiples
of `2π`. -/
theorem torusMap_add_int_mul_two_pi_right (θ φ : ℝ) (k : ℤ) :
    Work.Core.torusMap θ (φ + (k : ℝ) * (2 * Real.pi)) = Work.Core.torusMap θ φ :=
  (Work.Core.torusMap_eq_iff _ _ _ _).mpr ⟨⟨0, by simp⟩, ⟨k, by ring⟩⟩

/-- Two longitude circles of the standard torus with parameters not congruent modulo `2π` are
disjoint: their points are `torusMap θ a` and `torusMap θ' b`, and equality of two such points
forces `a ≡ b` modulo `2π` (`Work.Core.torusMap_eq_iff`). -/
theorem disjoint_range_longitudeCurve {a b : ℝ}
    (h : ∀ k : ℤ, b ≠ a + (k : ℝ) * (2 * Real.pi)) :
    Disjoint (Set.range (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard a).γ)
      (Set.range (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard b).γ) := by
  rw [Set.disjoint_left]
  rintro y ⟨θ, rfl⟩ ⟨θ', hθ'⟩
  have h1 : Work.Core.torusMap θ' b = Work.Core.torusMap θ a := hθ'
  obtain ⟨-, ⟨k, hk⟩⟩ := (Work.Core.torusMap_eq_iff _ _ _ _).mp h1
  exact h k hk

/-- **Membership in the trace of the horizontal plane `{z = v}`.**  A point of the standard torus
lies in the plane `{z = v}` exactly when it is `torusMap θ φ` with `sin φ = v`. -/
theorem mem_slice_z_iff {v : ℝ} {y : R3} :
    y ∈ {y : R3 | y 2 = v} ∩ Work.CoreTopology.standard.carrier ↔
      ∃ θ φ : ℝ, y = Work.Core.torusMap θ φ ∧ Real.sin φ = v := by
  constructor
  · rintro ⟨hyz, hyc⟩
    obtain ⟨θ, φ, hθφ⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff _ _).mp hyc
    refine ⟨θ, φ, hθφ.symm, ?_⟩
    have h2 : (Work.CoreTopology.standard.psi θ φ) 2 = v := by rw [hθφ]; exact hyz
    simpa [Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_two] using h2
  · rintro ⟨θ, φ, rfl, hφ⟩
    refine ⟨?_, ?_⟩
    · show (Work.Core.torusMap θ φ) 2 = v
      rw [Work.Core.torusMap_apply_two, hφ]
    · exact Work.CoreTopology.ParamTorus.psi_mem_carrier _ _ _

/-- **Covering the trace by two longitude circles.**  If every solution `ψ` of `sin ψ = v` is
congruent modulo `2π` to `a` or to `b`, then the trace `{z = v} ∩ F` of the standard torus is
covered by the longitude circles at the parameters `a` and `b`. -/
theorem slice_subset_two_longitudeCurves {v a b : ℝ}
    (h : ∀ ψ : ℝ, Real.sin ψ = v →
      (∃ k : ℤ, ψ = a + (k : ℝ) * (2 * Real.pi)) ∨
      (∃ k : ℤ, ψ = b + (k : ℝ) * (2 * Real.pi))) :
    {y : R3 | y 2 = v} ∩ Work.CoreTopology.standard.carrier ⊆
      Set.range (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard a).γ ∪
      Set.range (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard b).γ := by
  intro y hy
  obtain ⟨θ, φ, rfl, hφ⟩ := mem_slice_z_iff.mp hy
  rcases h φ hφ with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine ⟨θ, ?_⟩
    show Work.Core.torusMap θ a = Work.Core.torusMap θ φ
    rw [hk, torusMap_add_int_mul_two_pi_right]
  · right
    refine ⟨θ, ?_⟩
    show Work.Core.torusMap θ b = Work.Core.torusMap θ φ
    rw [hk, torusMap_add_int_mul_two_pi_right]

/-- **The trace of a plane normal to the axis of the standard torus is covered by a good family of
longitude circles.**  For any real `v` and any coprime positive `p`, `q` there are finitely many
pairwise disjoint simple closed curves on the standard torus, each either inessential or meeting
the standard `(p,q)`-curve in at least `min p q` points, whose union covers `{z = v} ∩ F`.

The curves are the longitude circles at the solutions of `sin φ = v`: at most two of them
(`arcsin v` and `π - arcsin v`), one when `v = ±1`, and none is needed when `|v| > 1`, where the
trace is empty.  Longitude circles are simple (`Work.CoreTopology.longitudeCurve_simple`), pairwise
disjoint for distinct parameters, and meet the `(p,q)`-curve in exactly `q ≥ min p q` points
(`Work.CoreTopology.encard_longitude_inter_standardCurve`). -/
theorem exists_traceCircleFamily_z (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (v : ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (C : ι → Work.CoreTopology.ClosedCurve Work.CoreTopology.standard),
      (Pairwise fun i j => Disjoint (Set.range (C i).γ) (Set.range (C j).γ)) ∧
      (∀ i, Work.CoreTopology.IsSimple Work.CoreTopology.standard (C i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential Work.CoreTopology.standard (C i) ∨
        (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range (Work.CoreTopology.standardCurve p q).γ ∩
          Set.range (C i).γ)) ∧
      ({y : LeanEval.KnotTheory.PardonDistortion.R3 | y 2 = v} ∩
        Work.CoreTopology.standard.carrier ⊆ ⋃ i, Set.range (C i).γ) := by
  by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1
  · have hsin_a : Real.sin (Real.arcsin v) = v := Real.sin_arcsin hv.1 hv.2
    -- every solution of `sin ψ = v` is congruent to `arcsin v` or to `π - arcsin v`
    have hcov : ∀ ψ : ℝ, Real.sin ψ = v →
        (∃ k : ℤ, ψ = Real.arcsin v + (k : ℝ) * (2 * Real.pi)) ∨
        (∃ k : ℤ, ψ = (Real.pi - Real.arcsin v) + (k : ℝ) * (2 * Real.pi)) := by
      intro ψ hψ
      have hsin : Real.sin (Real.arcsin v) = Real.sin ψ := by rw [hsin_a, hψ]
      obtain ⟨k, hk | hk⟩ := (Real.sin_eq_sin_iff (x := Real.arcsin v) (y := ψ)).mp hsin
      · left; exact ⟨k, by rw [hk]; ring⟩
      · right; exact ⟨k, by rw [hk]; ring⟩
    by_cases h1 : v = 1
    · -- `v = 1`: the two solutions coincide, one longitude circle suffices
      have hb' : Real.pi - Real.arcsin v = Real.arcsin v := by
        rw [h1, Real.arcsin_one]; ring
      have hcov1 : ∀ ψ : ℝ, Real.sin ψ = v →
          ∃ k : ℤ, ψ = Real.arcsin v + (k : ℝ) * (2 * Real.pi) := by
        intro ψ hψ
        rcases hcov ψ hψ with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨k, hk⟩
        · refine ⟨k, ?_⟩
          rw [hk, hb']
      let C : Fin 1 → Work.CoreTopology.ClosedCurve Work.CoreTopology.standard :=
        fun _ => Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.arcsin v)
      have hC0 : C 0 = Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.arcsin v) := rfl
      refine ⟨Fin 1, inferInstance, C, ?_, ?_, ?_, ?_⟩
      · intro i j hij; exact absurd (Subsingleton.elim i j) hij
      · rw [Fin.forall_fin_one, hC0]
        exact Work.CoreTopology.longitudeCurve_simple _ _
      · rw [Fin.forall_fin_one, hC0]
        right
        rw [Work.CoreTopology.encard_longitude_inter_standardCurve p q hp hq hc (Real.arcsin v)]
        exact_mod_cast Nat.min_le_right p q
      · intro y hy
        rw [Set.mem_iUnion]
        rcases slice_subset_two_longitudeCurves (v := v) (a := Real.arcsin v) (b := Real.arcsin v)
            (fun ψ hψ => Or.inl (hcov1 ψ hψ)) hy with hh | hh
        · exact ⟨0, by rw [hC0]; exact hh⟩
        · exact ⟨0, by rw [hC0]; exact hh⟩
    · by_cases hm1 : v = -1
      · -- `v = -1`: again a single longitude circle
        have hb' : Real.pi - Real.arcsin v = Real.arcsin v + 1 * (2 * Real.pi) := by
          rw [hm1, Real.arcsin_neg_one]; ring
        have hcov1 : ∀ ψ : ℝ, Real.sin ψ = v →
            ∃ k : ℤ, ψ = Real.arcsin v + (k : ℝ) * (2 * Real.pi) := by
          intro ψ hψ
          rcases hcov ψ hψ with ⟨k, hk⟩ | ⟨k, hk⟩
          · exact ⟨k, hk⟩
          · refine ⟨k + 1, ?_⟩
            rw [hk, hb']
            push_cast
            ring
        let C : Fin 1 → Work.CoreTopology.ClosedCurve Work.CoreTopology.standard :=
          fun _ => Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.arcsin v)
        have hC0 : C 0 = Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.arcsin v) := rfl
        refine ⟨Fin 1, inferInstance, C, ?_, ?_, ?_, ?_⟩
        · intro i j hij; exact absurd (Subsingleton.elim i j) hij
        · rw [Fin.forall_fin_one, hC0]
          exact Work.CoreTopology.longitudeCurve_simple _ _
        · rw [Fin.forall_fin_one, hC0]
          right
          rw [Work.CoreTopology.encard_longitude_inter_standardCurve p q hp hq hc (Real.arcsin v)]
          exact_mod_cast Nat.min_le_right p q
        · intro y hy
          rw [Set.mem_iUnion]
          rcases slice_subset_two_longitudeCurves (v := v) (a := Real.arcsin v) (b := Real.arcsin v)
              (fun ψ hψ => Or.inl (hcov1 ψ hψ)) hy with hh | hh
          · exact ⟨0, by rw [hC0]; exact hh⟩
          · exact ⟨0, by rw [hC0]; exact hh⟩
      · -- the generic case: two distinct longitude circles at `arcsin v` and `π - arcsin v`
        have ha_lt : Real.arcsin v < Real.pi / 2 :=
          Real.arcsin_lt_pi_div_two.mpr (lt_of_le_of_ne hv.2 h1)
        have ha_gt : -(Real.pi / 2) < Real.arcsin v :=
          Real.neg_pi_div_two_lt_arcsin.mpr (lt_of_le_of_ne hv.1 (Ne.symm hm1))
        have hB_pos : 0 < Real.pi - 2 * Real.arcsin v := by linarith
        have hB_lt : Real.pi - 2 * Real.arcsin v < 2 * Real.pi := by linarith
        have hne : ∀ k : ℤ, Real.pi - Real.arcsin v ≠ Real.arcsin v + (k : ℝ) * (2 * Real.pi) := by
          intro k hk
          have hB : (k : ℝ) * (2 * Real.pi) = Real.pi - 2 * Real.arcsin v := by linarith
          have hkpos : (0 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos, hB_pos]
          have hklt : (k : ℝ) < 1 := by nlinarith [Real.pi_pos, hB_lt]
          have hz : (0 : ℤ) < k := by exact_mod_cast hkpos
          have ho : k < 1 := by exact_mod_cast hklt
          omega
        have hne' : ∀ k : ℤ, Real.arcsin v ≠ (Real.pi - Real.arcsin v) + (k : ℝ) * (2 * Real.pi) := by
          intro k hk
          exact hne (-k) (by push_cast at hk ⊢; linarith)
        let C : Fin 2 → Work.CoreTopology.ClosedCurve Work.CoreTopology.standard :=
          fun i => if (i : ℕ) = 0
            then Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.arcsin v)
            else Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.pi - Real.arcsin v)
        have hC0 : C 0 = Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.arcsin v) := by
          simp [C]
        have hC1 : C 1 = Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (Real.pi - Real.arcsin v) := by
          simp [C]
        refine ⟨Fin 2, inferInstance, C, ?_, ?_, ?_, ?_⟩
        · intro i j hij
          have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
          obtain rfl | rfl := hi
          · obtain rfl | rfl := hj
            · exact absurd rfl hij
            · rw [hC0, hC1]; exact disjoint_range_longitudeCurve hne
          · obtain rfl | rfl := hj
            · rw [hC1, hC0]; exact disjoint_range_longitudeCurve hne'
            · exact absurd rfl hij
        · rw [Fin.forall_fin_two]; constructor
          · rw [hC0]; exact Work.CoreTopology.longitudeCurve_simple _ _
          · rw [hC1]; exact Work.CoreTopology.longitudeCurve_simple _ _
        · rw [Fin.forall_fin_two]; constructor
          · right
            rw [hC0, Work.CoreTopology.encard_longitude_inter_standardCurve p q hp hq hc (Real.arcsin v)]
            exact_mod_cast Nat.min_le_right p q
          · right
            rw [hC1, Work.CoreTopology.encard_longitude_inter_standardCurve p q hp hq hc (Real.pi - Real.arcsin v)]
            exact_mod_cast Nat.min_le_right p q
        · intro y hy
          rw [Set.mem_iUnion]
          rcases slice_subset_two_longitudeCurves (v := v) (a := Real.arcsin v)
              (b := Real.pi - Real.arcsin v) hcov hy with hh | hh
          · exact ⟨0, by rw [hC0]; exact hh⟩
          · exact ⟨1, by rw [hC1]; exact hh⟩
  · -- `|v| > 1`: the trace is empty, so the empty family covers it
    refine ⟨Fin 0, inferInstance, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro y hy
      obtain ⟨θ, φ, -, hφ⟩ := mem_slice_z_iff.mp hy
      exact absurd (show v ∈ Set.Icc (-1 : ℝ) 1 from by
        rw [← hφ]; exact ⟨Real.neg_one_le_sin φ, Real.sin_le_one φ⟩) hv

end

end Work.PinchCounted
