import Mathlib.Topology.Algebra.Ring.Real

namespace Commons.Topology.Homeomorph

open Set

theorem open_interval_affine {a b c d : ℝ} (hb : a < b) (hd : c < d) :
    Nonempty ({x : ℝ // x ∈ Set.Ioo a b} ≃ₜ {x : ℝ // x ∈ Set.Ioo c d}) := by
  let S : Type := {x : ℝ // x ∈ Set.Ioo a b}
  let T : Type := {y : ℝ // y ∈ Set.Ioo c d}
  let F : ℝ → ℝ := fun x => c + (x - a) / (b - a) * (d - c)
  let G : ℝ → ℝ := fun y => a + (y - c) / (d - c) * (b - a)
  have hF_mem : ∀ x : ℝ, x ∈ Set.Ioo a b → F x ∈ Set.Ioo c d := by
    intro x hx
    have hxa : a < x := hx.1
    have hxb : x < b := hx.2
    constructor
    · unfold F
      have hbapos : 0 < b - a := by linarith
      have h1 : 0 < (x - a) / (b - a) := div_pos (by linarith) hbapos
      have h2 : 0 < d - c := by linarith
      have h3 : 0 < (x - a) / (b - a) * (d - c) := mul_pos h1 h2
      linarith
    · unfold F
      have hbapos : 0 < b - a := by linarith
      have hdcpos : 0 < d - c := by linarith
      have hdiv : (x - a) / (b - a) < 1 := by
        rw [div_lt_one hbapos]
        linarith
      have hlt : (x - a) / (b - a) * (d - c) < d - c := by
        simpa using (mul_lt_mul_of_pos_right hdiv hdcpos)
      linarith
  have hG_mem : ∀ y : ℝ, y ∈ Set.Ioo c d → G y ∈ Set.Ioo a b := by
    intro y hy
    have hyc : c < y := hy.1
    have hyd : y < d := hy.2
    constructor
    · unfold G
      have hdcpos : 0 < d - c := by linarith
      have h1 : 0 < (y - c) / (d - c) := div_pos (by linarith) hdcpos
      have h2 : 0 < b - a := by linarith
      have h3 : 0 < (y - c) / (d - c) * (b - a) := mul_pos h1 h2
      linarith
    · unfold G
      have hbapos : 0 < b - a := by linarith
      have hdcpos : 0 < d - c := by linarith
      have hdiv : (y - c) / (d - c) < 1 := by
        rw [div_lt_one hdcpos]
        linarith
      have hlt : (y - c) / (d - c) * (b - a) < b - a := by
        simpa using (mul_lt_mul_of_pos_right hdiv hbapos)
      linarith
  have hFG : ∀ y : ℝ, y ∈ Set.Ioo c d → F (G y) = y := by
    intro y _
    unfold F G
    have hb_ne : b - a ≠ 0 := by linarith
    have hd_ne : d - c ≠ 0 := by linarith
    field_simp [hb_ne, hd_ne]
    ring
  have hGF : ∀ x : ℝ, x ∈ Set.Ioo a b → G (F x) = x := by
    intro x _
    unfold F G
    have hb_ne : b - a ≠ 0 := by linarith
    have hd_ne : d - c ≠ 0 := by linarith
    field_simp [hb_ne, hd_ne]
    ring
  have hF_cont : Continuous F := by fun_prop
  have hG_cont : Continuous G := by fun_prop
  let e : S ≃ T :=
    { toFun := Subtype.map F hF_mem
      invFun := Subtype.map G hG_mem
      left_inv := by
        intro x
        apply Subtype.ext
        exact hGF x.1 x.2
      right_inv := by
        intro y
        apply Subtype.ext
        exact hFG y.1 y.2 }
  refine ⟨Homeomorph.mk e ?_ ?_⟩
  · exact Continuous.subtype_map hF_cont hF_mem
  · exact Continuous.subtype_map hG_cont hG_mem

end Commons.Topology.Homeomorph