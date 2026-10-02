import Submission.Work.FlowerGlue.cyl_end_bdd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue

open Complex Function Filter
open scoped Real Topology

noncomputable section

/-- See `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.1 (lemmas C1-C4) for the full proof plan. -/
theorem cyl_rigid {T : ℂ → ℂ} (hT : Differentiable ℂ T) (hinj : Function.Injective T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) : ∃ s : ℂ, ∀ ζ : ℂ, T ζ = ζ + s := by
  obtain ⟨Y, M, hM⟩ := cyl_end_bdd hT hinj hper
  have hT'diff : Differentiable ℂ (fun ζ : ℂ => -T (-ζ)) := by fun_prop
  have hT'inj : Function.Injective (fun ζ : ℂ => -T (-ζ)) := by
    intro a b h
    have h' : T (-a) = T (-b) := by simpa using h
    have := hinj h'
    simpa using this
  have hT'per : ∀ ζ : ℂ, (fun ζ : ℂ => -T (-ζ)) (ζ + 1) = (fun ζ : ℂ => -T (-ζ)) ζ + 1 := by
    intro ζ
    have h1 : T (-ζ - 1) = T (-ζ) - 1 := by
      have := hper (-ζ - 1)
      rw [show -ζ - 1 + 1 = -ζ from by ring] at this
      rw [this]; ring
    show -T (-(ζ + 1)) = -T (-ζ) + 1
    rw [show -(ζ + 1) = -ζ - 1 from by ring, h1]; ring
  obtain ⟨Y', M', hM'⟩ := cyl_end_bdd hT'diff hT'inj hT'per
  set B : ℂ → ℂ := fun ζ => T ζ - ζ with hBdef
  have hBdiff : Differentiable ℂ B := by rw [hBdef]; fun_prop
  have hBper : Function.Periodic B 1 := by
    intro ζ
    rw [hBdef]
    show T (ζ + 1) - (ζ + 1) = T ζ - ζ
    rw [hper ζ]; ring
  have hBup : ∀ ζ : ℂ, Y < ζ.im → ‖B ζ‖ ≤ M := by
    intro ζ hζ
    rw [hBdef]; exact hM ζ hζ
  have hBlow : ∀ η : ℂ, η.im < -Y' → ‖B η‖ ≤ M' := by
    intro η hη
    have hle : Y' < (-η).im := by rw [Complex.neg_im]; linarith
    have h := hM' (-η) hle
    have heq : (fun ζ : ℂ => -T (-ζ)) (-η) - (-η) = -(B η) := by
      rw [hBdef]; simp only; ring
    rw [heq, norm_neg] at h
    exact h
  obtain ⟨C, hC⟩ : ∃ C, ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) (|Y| + |Y'| + 2) → ‖B z‖ ≤ C := by
    have himg : IsCompact (B '' Metric.closedBall (0 : ℂ) (|Y| + |Y'| + 2)) :=
      (isCompact_closedBall (0 : ℂ) (|Y| + |Y'| + 2)).image hBdiff.continuous
    have hb : Bornology.IsBounded (B '' Metric.closedBall (0 : ℂ) (|Y| + |Y'| + 2)) :=
      himg.isBounded
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (B 0)).mp hb
    refine ⟨r + ‖B 0‖, ?_⟩
    intro z hz
    have hmem : B z ∈ Metric.closedBall (B 0) r := hr ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    calc ‖B z‖ = ‖(B z - B 0) + B 0‖ := by ring_nf
      _ ≤ ‖B z - B 0‖ + ‖B 0‖ := norm_add_le _ _
      _ ≤ r + ‖B 0‖ := by linarith
  have hBglob : ∀ ζ : ℂ, ‖B ζ‖ ≤ max (max M M') C := by
    intro ζ
    set ξ : ℂ := ζ - ((⌊ζ.re⌋ : ℤ) : ℂ) with hξ
    have hξre : ξ.re = Int.fract ζ.re := by
      rw [hξ, Complex.sub_re, ← Complex.ofReal_intCast, Complex.ofReal_re, Int.fract]
    have hξim : ξ.im = ζ.im := by
      rw [hξ, Complex.sub_im, ← Complex.ofReal_intCast, Complex.ofReal_im, sub_zero]
    have hζeq : ζ = ξ + ((⌊ζ.re⌋ : ℤ) : ℂ) := by rw [hξ]; ring
    have hBξ : B ζ = B ξ := by
      rw [hζeq]
      have h := hBper.int_mul ⌊ζ.re⌋ ξ
      rw [mul_one] at h
      exact h
    rw [hBξ]
    by_cases hY : Y < ζ.im
    · exact le_trans (hBup ξ (by rw [hξim]; exact hY))
        (le_trans (le_max_left M M') (le_max_left (max M M') C))
    · push_neg at hY
      by_cases hY' : ζ.im < -Y'
      · exact le_trans (hBlow ξ (by rw [hξim]; exact hY'))
          (le_trans (le_max_right M M') (le_max_left (max M M') C))
      · push_neg at hY'
        have hξmem : ξ ∈ Metric.closedBall (0 : ℂ) (|Y| + |Y'| + 2) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hξre_nn : 0 ≤ ξ.re := by rw [hξre]; exact Int.fract_nonneg _
          have hξre_lt : ξ.re < 1 := by rw [hξre]; exact Int.fract_lt_one _
          have him_abs : |ζ.im| ≤ |Y| + |Y'| := by
            rw [abs_le]
            exact ⟨by linarith [hY', le_abs_self Y', abs_nonneg Y],
                   by linarith [hY, le_abs_self Y, abs_nonneg Y']⟩
          calc ‖ξ‖ ≤ |ξ.re| + |ξ.im| := Complex.norm_le_abs_re_add_abs_im ξ
            _ = ξ.re + |ζ.im| := by rw [abs_of_nonneg hξre_nn, hξim]
            _ ≤ 1 + (|Y| + |Y'|) := by
                have : ξ.re ≤ 1 := le_of_lt hξre_lt
                linarith
            _ ≤ |Y| + |Y'| + 2 := by linarith
        exact le_trans (hC ξ hξmem) (le_max_right (max M M') C)
  have hBdd : Bornology.IsBounded (Set.range B) :=
    Bornology.IsBounded.subset (isCompact_closedBall (0 : ℂ) (max (max M M') C)).isBounded
      (fun w ⟨ζ, hζ⟩ => by
        rw [← hζ, Metric.mem_closedBall, dist_zero_right]
        exact hBglob ζ)
  refine ⟨T 0, fun ζ => ?_⟩
  have hconst : B ζ = B 0 := hBdiff.apply_eq_apply_of_bounded hBdd ζ 0
  rw [hBdef] at hconst
  simp only at hconst
  calc T ζ = (T ζ - ζ) + ζ := by ring
    _ = T 0 + ζ := by rw [hconst]; ring_nf
    _ = ζ + T 0 := by ring

end

end Work.FlowerGlue
