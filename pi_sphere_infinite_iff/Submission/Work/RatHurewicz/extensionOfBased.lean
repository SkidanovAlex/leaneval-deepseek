import Mathlib
import Submission.Work.RatHurewicz.PinchGeom
import Submission.Work.RatHurewicz.FillFamilyDefs
import Submission.Work.ThomBordism.TwoSet.ConeDescent

/-!
# Filling a pinched cube boundary from a based null-homotopy

`Work.RatHurewicz.extensionOfBased`: a continuous `B` on `∂I^{m+1}` which is `x₀` on the bottom
face `{z_last = 0}` extends over `I^{m+1}` as soon as a *based* null-homotopy of `B ∘ iota` is
given, relative to `∂I^m`.

The pinch pair `iota`/`psiBd` (`PinchGeom`) identifies `I^m` with the complement of the open
bottom face ("the dome") and inverts it off that face.  The homotopy

`H (z, s) = G (s, psiBd z)`  (`z` off the rim of the bottom face),  `H (z, s) = x₀`  (in the
interior of the bottom face)

is continuous (the two formulas agree on the rim, where `psiBd z ∈ ∂I^m` and `G` is constant
`x₀`), starts at `B` and ends at the constant map, so `ConeDescent` turns it into the required
extension.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem extensionOfBased {m : ℕ} (hm : 1 ≤ m) {X : Type} [TopologicalSpace X]
    (x₀ : X) (B : C(↥(Cube.boundary (Fin (m + 1))), X)) (G : C(unitInterval × IC m, X))
    (hB : ∀ z : ↥(Cube.boundary (Fin (m + 1))), (z : IC (m + 1)) (Fin.last m) = 0 → B z = x₀)
    (hG0 : ∀ u : IC m, G (0, u) = B (iota m hm u))
    (hG1 : ∀ u : IC m, G (1, u) = x₀)
    (hG2 : ∀ u ∈ Cube.boundary (Fin m), ∀ s : unitInterval, G (s, u) = x₀)
    (hpsi1 : ∀ z : ↥(Cube.boundary (Fin (m + 1))), (z : IC (m + 1)) (Fin.last m) ≠ 0 →
      iota m hm (psiBd m z) = z)
    (hpsi2 : ∀ z : ↥(Cube.boundary (Fin (m + 1))), (z : IC (m + 1)) (Fin.last m) = 0 →
      (∃ j : Fin m, (z : IC (m + 1)) (Fin.castSucc j) = 0 ∨ (z : IC (m + 1)) (Fin.castSucc j) = 1) →
      psiBd m z ∈ Cube.boundary (Fin m)) :
    ∃ F : C(IC (m + 1), X), ∀ z : ↥(Cube.boundary (Fin (m + 1))), F z = B z := by
  classical
  -- the interior of the bottom face
  let U : Set ↥(Cube.boundary (Fin (m + 1))) :=
    {z | (z : IC (m + 1)) (Fin.last m) = 0 ∧
      ∀ j : Fin m, (z : IC (m + 1)) (Fin.castSucc j) ≠ 0 ∧
        (z : IC (m + 1)) (Fin.castSucc j) ≠ 1}
  have hUopen : IsOpen U := by
    have hW : IsOpen {w : IC (m + 1) |
        (∀ j : Fin m, ((w (Fin.castSucc j) : unitInterval) : ℝ) ∈ Set.Ioo 0 1) ∧
        ((w (Fin.last m) : unitInterval) : ℝ) < 1/2} := by
      have hset : (fun w : IC (m + 1) =>
            ∀ j : Fin m, ((w (Fin.castSucc j) : unitInterval) : ℝ) ∈ Set.Ioo 0 1)
          = ⋂ j : Fin m, {w : IC (m + 1) | ((w (Fin.castSucc j) : unitInterval) : ℝ) ∈ Set.Ioo 0 1} := by
        funext w
        exact propext ⟨fun h => Set.mem_iInter.mpr h, fun h => Set.mem_iInter.mp h⟩
      refine IsOpen.inter ?_ ?_
      · rw [hset]
        exact isOpen_iInter_of_finite fun j => isOpen_Ioo.preimage
          (by fun_prop : Continuous fun w : IC (m + 1) =>
            ((w (Fin.castSucc j) : unitInterval) : ℝ))
      · exact isOpen_Iio.preimage
          (by fun_prop : Continuous fun w : IC (m + 1) =>
            ((w (Fin.last m) : unitInterval) : ℝ))
    have hUeq : U = Subtype.val ⁻¹' {w : IC (m + 1) |
        (∀ j : Fin m, ((w (Fin.castSucc j) : unitInterval) : ℝ) ∈ Set.Ioo 0 1) ∧
        ((w (Fin.last m) : unitInterval) : ℝ) < 1/2} := by
      ext z; constructor
      · intro hz
        obtain ⟨h0, hj⟩ := hz
        refine ⟨fun j => ?_, ?_⟩
        · have h1 : ((z : IC (m + 1)) (Fin.castSucc j) : ℝ) ≠ 0 := by
            intro h; exact (hj j).1 (Subtype.ext h)
          have h2 : ((z : IC (m + 1)) (Fin.castSucc j) : ℝ) ≠ 1 := by
            intro h; exact (hj j).2 (Subtype.ext h)
          have hle : ((z : IC (m + 1)) (Fin.castSucc j) : ℝ) ≤ 1 :=
            ((z : IC (m + 1)) (Fin.castSucc j)).2.2
          have hge : (0:ℝ) ≤ ((z : IC (m + 1)) (Fin.castSucc j) : ℝ) :=
            ((z : IC (m + 1)) (Fin.castSucc j)).2.1
          exact ⟨lt_of_le_of_ne hge (Ne.symm h1), lt_of_le_of_ne hle h2⟩
        · rw [h0]; norm_num
      · rintro ⟨h1, h2⟩
        have hz2 := z.2
        have hlast : (z : IC (m + 1)) (Fin.last m) = 0 := by
          obtain ⟨i, hi⟩ := hz2
          rcases hi with h | h
          · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
            · exact absurd (by simpa using congrArg Subtype.val h) (ne_of_gt (h1 j).1)
            · exact h
          · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
            · exact absurd (by simpa using congrArg Subtype.val h) (ne_of_lt (h1 j).2)
            · exfalso
              have h3 : ((z : IC (m + 1)) (Fin.last m) : ℝ) = 1 := by rw [h]; rfl
              rw [h3] at h2
              norm_num at h2
        refine ⟨hlast, fun j => ⟨?_, ?_⟩⟩
        · intro h; exact ne_of_gt (h1 j).1 (congrArg Subtype.val h)
        · intro h; exact ne_of_lt (h1 j).2 (congrArg Subtype.val h)
    rw [hUeq]
    exact hW.preimage continuous_subtype_val
  -- the closed pieces
  have hUc_closed : IsClosed Uᶜ := hUopen.isClosed_compl
  have hlast_zero_closed : IsClosed {z : ↥(Cube.boundary (Fin (m + 1))) |
      (z : IC (m + 1)) (Fin.last m) = 0} :=
    isClosed_eq ((continuous_apply (Fin.last m)).comp continuous_subtype_val) continuous_const
  have hclosure_last : closure U ⊆ {z : ↥(Cube.boundary (Fin (m + 1))) |
      (z : IC (m + 1)) (Fin.last m) = 0} :=
    closure_minimal (fun z hz => hz.1) hlast_zero_closed
  -- the witness for points of the rim
  have hrim : ∀ z ∈ closure U, z ∉ U →
      ∃ j : Fin m, (z : IC (m + 1)) (Fin.castSucc j) = 0 ∨
        (z : IC (m + 1)) (Fin.castSucc j) = 1 := by
    intro z hz hzU
    have h0 : (z : IC (m + 1)) (Fin.last m) = 0 := hclosure_last hz
    by_contra hcon
    push_neg at hcon
    exact hzU ⟨h0, fun j => ⟨fun h => (hcon j).1 h, fun h => (hcon j).2 h⟩⟩
  -- the candidate homotopy
  let Hfun : ↥(Cube.boundary (Fin (m + 1))) × unitInterval → X :=
    fun q => if q.1 ∈ U then x₀ else G (q.2, psiBd m q.1)
  have hH_const : ∀ q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval, q.1 ∈ closure U →
      Hfun q = x₀ := by
    intro q hq
    by_cases hqU : q.1 ∈ U
    · simp only [Hfun, if_pos hqU]
    · simp only [Hfun, if_neg hqU]
      exact hG2 _ (hpsi2 q.1 (hclosure_last hq) (hrim q.1 hq hqU)) q.2
  have hH_G : ∀ q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval, q.1 ∈ Uᶜ →
      Hfun q = G (q.2, psiBd m q.1) := by
    intro q hq
    simp only [Hfun, if_neg hq]
  have hcont : Continuous Hfun := by
    have h1 : ContinuousOn Hfun
        {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U}ᶜ := by
      refine ContinuousOn.congr ?_ (fun q hq => hH_G q hq)
      exact (G.continuous.comp (Continuous.prodMk continuous_snd
        ((psiBd m).continuous.comp continuous_fst))).continuousOn
    have h2 : ContinuousOn Hfun
        (closure {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U}) := by
      refine ContinuousOn.congr
        (f := fun _ : ↥(Cube.boundary (Fin (m + 1))) × unitInterval => x₀)
        continuousOn_const (fun q hq => ?_)
      have hcl : IsClosed {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ closure U} :=
        isClosed_closure.preimage continuous_fst
      have hq' : q.1 ∈ closure U :=
        closure_minimal (s := {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U})
          (t := {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ closure U})
          (fun q hq => subset_closure hq) hcl hq
      exact hH_const q hq' 
    have h3 : ContinuousOn Hfun
        ({q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U}ᶜ ∪
          closure {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U}) :=
      ContinuousOn.union_of_isClosed h1 h2 (hUopen.preimage continuous_fst).isClosed_compl
        isClosed_closure
    rw [show ({q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U}ᶜ ∪
          closure {q : ↥(Cube.boundary (Fin (m + 1))) × unitInterval | q.1 ∈ U}) = Set.univ from
        Set.eq_univ_of_forall fun q => by
          by_cases h : q.1 ∈ U
          · exact Or.inr (subset_closure h)
          · exact Or.inl h] at h3
    exact continuousOn_univ.mp h3
  -- the endpoints
  have hH0 : ∀ z : ↥(Cube.boundary (Fin (m + 1))), Hfun (z, 0) = B z := by
    intro z
    by_cases hzU : z ∈ U
    · simp only [Hfun, if_pos hzU]
      exact (hB z hzU.1).symm
    · simp only [Hfun, if_neg hzU]
      by_cases hz0 : (z : IC (m + 1)) (Fin.last m) = 0
      · rw [hB z hz0]
        exact hG2 _ (hpsi2 z hz0 (by
          by_contra hcon
          push_neg at hcon
          exact hzU ⟨hz0, fun j => ⟨fun h => (hcon j).1 h, fun h => (hcon j).2 h⟩⟩)) 0
      · rw [hG0 (psiBd m z), hpsi1 z hz0]
  have hH1 : ∀ z : ↥(Cube.boundary (Fin (m + 1))), Hfun (z, 1) = x₀ := by
    intro z
    by_cases hzU : z ∈ U
    · simp only [Hfun, if_pos hzU]
    · simp only [Hfun, if_neg hzU]
      exact hG1 (psiBd m z)
  obtain ⟨F, hF⟩ := Work.ThomBordism.TwoSet.ConeDescent (m := m + 1) (Nat.le_add_left 1 m) (y₀ := x₀)
    ⟨Hfun, hcont⟩ hH1
  exact ⟨F, fun z => by rw [hF z]; exact hH0 z⟩

end

end Work.RatHurewicz
