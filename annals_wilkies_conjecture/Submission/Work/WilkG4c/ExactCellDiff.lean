import Mathlib
import Submission.Work.WilkG4c.ExactCellDefs
import Submission.Work.WilkG4c.mem_Ioo_min_max_of_injOn

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- **Differentiability of the charted family, with derivative bounded by `1`.**  `f` is the
dominating member of the family, `fa a` are the members and `df`, `dfa a` their derivatives along
the fibre; `|df| ≥ 1` and `|dfa a| ≤ |df|` pointwise on the fibre.  Then for every member the
composite `τ ↦ fa a (chartVal g α β l (fun _ => τ))` is differentiable on `(0,1)` with derivative
bounded by `1` in absolute value. -/
theorem exactCell_diff {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    {g : (Fin (p + 1) → ℝ) → ℝ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    {ι : Type*} (fa : ι → ℝ → ℝ) (dfa : ι → ℝ → ℝ) (df : ℝ → ℝ)
    (hF : CellFacts κ f g α β l)
    (hcontf : ∀ x : ℝ, Fin.snoc l x ∈ κ → ContinuousAt (fun s : ℝ => f (Fin.snoc l s)) x)
    (hdf : ∀ x : ℝ, Fin.snoc l x ∈ κ → HasDerivAt (fun s : ℝ => f (Fin.snoc l s)) (df x) x)
    (hdfge : ∀ x : ℝ, Fin.snoc l x ∈ κ → 1 ≤ |df x|)
    (hdfa : ∀ (a : ι) (x : ℝ), Fin.snoc l x ∈ κ → HasDerivAt (fa a) (dfa a x) x)
    (hdfale : ∀ (a : ι) (x : ℝ), Fin.snoc l x ∈ κ → |dfa a x| ≤ |df x|) :
    ∀ (a : ι) (τ : ℝ), τ ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun τ' : ℝ => fa a (chartVal g α β l (fun _ => τ'))) τ ∧
      |deriv (fun τ' : ℝ => fa a (chartVal g α β l (fun _ => τ'))) τ| ≤ 1 := by
  intro a τ hτ
  obtain ⟨s, hs1, hs2⟩ := hF.img τ hτ
  have hgv : g (Fin.snoc l (α l + τ * (β l - α l))) = s :=
    hF.inv_eq (α l + τ * (β l - α l)) s (by rw [mem_invSet]; exact ⟨hs1, hs2⟩)
  by_cases hlt : α l < β l
  · -- non-degenerate case: `g` is differentiable and inverts `f`
    obtain ⟨A, B, hAB, hKAB⟩ := hF.interval hlt
    have hsAB : s ∈ Set.Ioo A B := by rw [← hKAB]; exact hs1
    have hstr := hF.strict hlt s hs1
    have hcontG : ContinuousAt (fun η : ℝ => g (Fin.snoc l η)) (α l + τ * (β l - α l)) := by
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hm1 : max A (s - ε) < s := max_lt hsAB.1 (by linarith)
      obtain ⟨sm, hsm1, hsm2⟩ := exists_between hm1
      have hAsm : A < sm := lt_of_le_of_lt (le_max_left _ _) hsm1
      have hsmε : s - ε < sm := lt_of_le_of_lt (le_max_right _ _) hsm1
      have hm2 : s < min B (s + ε) := lt_min hsAB.2 (by linarith)
      obtain ⟨sp, hsp1, hsp2⟩ := exists_between hm2
      have hspB : sp < B := lt_of_lt_of_le hsp2 (min_le_left _ _)
      have hspε : sp < s + ε := lt_of_lt_of_le hsp2 (min_le_right _ _)
      have hsmK : Fin.snoc l sm ∈ κ := by
        have h : sm ∈ ({s : ℝ | Fin.snoc l s ∈ κ}) := by
          rw [hKAB]; exact ⟨hAsm, lt_trans hsm2 hsAB.2⟩
        exact h
      have hspK : Fin.snoc l sp ∈ κ := by
        have h : sp ∈ ({s : ℝ | Fin.snoc l s ∈ κ}) := by
          rw [hKAB]; exact ⟨lt_trans hsAB.1 hsp1, hspB⟩
        exact h
      have hsubK : Set.Icc sm sp ⊆ {s : ℝ | Fin.snoc l s ∈ κ} := by
        intro x hx
        have h : x ∈ ({s : ℝ | Fin.snoc l s ∈ κ}) := by
          rw [hKAB]
          exact ⟨lt_of_lt_of_le hAsm hx.1, lt_of_le_of_lt hx.2 hspB⟩
        exact h
      have hcontI : ContinuousOn (fun s : ℝ => f (Fin.snoc l s)) (Set.Icc sm sp) :=
        fun x hx => (hcontf x (hsubK hx)).continuousWithinAt
      have hinjI : Set.InjOn (fun s : ℝ => f (Fin.snoc l s)) (Set.Icc sm sp) := by
        intro x hx y hy hxy
        exact hF.inj x y (hsubK hx) (hsubK hy) hxy
      have hmemI : f (Fin.snoc l s) ∈
          Set.Ioo (min (f (Fin.snoc l sm)) (f (Fin.snoc l sp)))
            (max (f (Fin.snoc l sm)) (f (Fin.snoc l sp))) :=
        mem_Ioo_min_max_of_injOn hsm2 hsp1 hcontI hinjI
      set δ : ℝ := min (f (Fin.snoc l s) - min (f (Fin.snoc l sm)) (f (Fin.snoc l sp)))
        (max (f (Fin.snoc l sm)) (f (Fin.snoc l sp)) - f (Fin.snoc l s)) with hδdef
      have hδ : 0 < δ := by
        rw [hδdef]
        exact lt_min (sub_pos.mpr hmemI.1) (sub_pos.mpr hmemI.2)
      have hδ1 : δ ≤ f (Fin.snoc l s) - min (f (Fin.snoc l sm)) (f (Fin.snoc l sp)) := by
        rw [hδdef]; exact min_le_left _ _
      have hδ2 : δ ≤ max (f (Fin.snoc l sm)) (f (Fin.snoc l sp)) - f (Fin.snoc l s) := by
        rw [hδdef]; exact min_le_right _ _
      refine ⟨δ, hδ, fun y hy => ?_⟩
      have hy1 : |y - f (Fin.snoc l s)| < δ := by
        rw [Real.dist_eq] at hy
        simpa [show α l + τ * (β l - α l) = f (Fin.snoc l s) from hs2.symm] using hy
      have hyne : y ∈ Set.Ioo (min (f (Fin.snoc l sm)) (f (Fin.snoc l sp)))
          (max (f (Fin.snoc l sm)) (f (Fin.snoc l sp))) := by
        have hylt : y - f (Fin.snoc l s) < δ := (abs_lt.mp hy1).2
        have hygt : -(y - f (Fin.snoc l s)) < δ := by linarith [(abs_lt.mp hy1).1]
        refine ⟨?_, ?_⟩
        · have hh : f (Fin.snoc l s) - δ < y := by linarith
          have hh2 : min (f (Fin.snoc l sm)) (f (Fin.snoc l sp))
              ≤ f (Fin.snoc l s) - δ := by linarith
          linarith
        · have hh : y < f (Fin.snoc l s) + δ := by linarith
          have hh2 : f (Fin.snoc l s) + δ
              ≤ max (f (Fin.snoc l sm)) (f (Fin.snoc l sp)) := by linarith
          linarith
      obtain ⟨x, hxIcc, hxy⟩ := exists_eq_of_mem_Ioo_min_max
        (le_of_lt (lt_trans hsm2 hsp1)) hcontI hyne
      have hKx : Fin.snoc l x ∈ κ := hsubK hxIcc
      have hGy : g (Fin.snoc l y) = x :=
        hF.inv_eq y x (by rw [mem_invSet]; exact ⟨hKx, hxy⟩)
      rw [hGy, hgv, Real.dist_eq, abs_lt]
      have hx1 : sm ≤ x := hxIcc.1
      have hx2 : x ≤ sp := hxIcc.2
      constructor <;> linarith
    have hf'_ge : 1 ≤ |df s| := hdfge s hs1
    have hf'_pos : 0 < |df s| := lt_of_lt_of_le one_pos hf'_ge
    have hGdiff : HasDerivAt (fun η : ℝ => g (Fin.snoc l η)) (df s)⁻¹
        (α l + τ * (β l - α l)) := by
      refine HasDerivAt.of_local_left_inverse
        (f := fun s : ℝ => f (Fin.snoc l s))
        (g := fun η : ℝ => g (Fin.snoc l η))
        (a := α l + τ * (β l - α l)) hcontG ?_ ?_ ?_
      · have hd : HasDerivAt (fun s : ℝ => f (Fin.snoc l s)) (df s)
            (g (Fin.snoc l (α l + τ * (β l - α l)))) := by
          rw [hgv]
          exact hdf s hs1
        exact hd
      · exact abs_pos.mp (lt_of_lt_of_le one_pos hf'_ge)
      have hη₀I : α l + τ * (β l - α l) ∈ Set.Ioo (α l) (β l) := by
        constructor
        · rw [← hs2]; exact hstr.1
        · rw [← hs2]; exact hstr.2
      filter_upwards [isOpen_Ioo.mem_nhds hη₀I] with y hy
      obtain ⟨x, hx1, hx2⟩ := hF.ivt y hy.1 hy.2
      have hgx : g (Fin.snoc l y) = x :=
        hF.inv_eq y x (by rw [mem_invSet]; exact ⟨hx1, hx2⟩)
      rw [hgx]
      exact hx2
    have hAdiff : HasDerivAt (fun τ' : ℝ => α l + τ' * (β l - α l)) (β l - α l) τ := by
      have h := ((hasDerivAt_id τ).mul_const (β l - α l)).const_add (α l)
      simpa using h
    have hψ : HasDerivAt (fun τ' : ℝ => chartVal g α β l (fun _ => τ'))
        ((df s)⁻¹ * (β l - α l)) τ := by
      have h := hGdiff.comp τ hAdiff
      have heqfun : ((fun η : ℝ => g (Fin.snoc l η)) ∘ fun τ' : ℝ => α l + τ' * (β l - α l)) =
          (fun τ' : ℝ => chartVal g α β l (fun _ => τ')) := funext (fun τ' => rfl)
      rw [heqfun] at h
      exact h
    have hfa' : HasDerivAt (fa a) (dfa a s)
        ((fun τ' : ℝ => chartVal g α β l (fun _ => τ')) τ) := by
      have hτv : (fun τ' : ℝ => chartVal g α β l (fun _ => τ')) τ
          = g (Fin.snoc l (α l + τ * (β l - α l))) := rfl
      rw [hτv, hgv]
      exact hdfa a s hs1
    refine ⟨(hfa'.comp τ hψ).differentiableAt, ?_⟩
    have hderiv : deriv (fun τ' : ℝ => fa a (chartVal g α β l (fun _ => τ'))) τ
        = dfa a s * ((df s)⁻¹ * (β l - α l)) := by
      have h := hfa'.comp τ hψ
      have heq2 : (fun τ' : ℝ => fa a (chartVal g α β l (fun _ => τ'))) =
          fa a ∘ (fun τ' : ℝ => chartVal g α β l (fun _ => τ')) := rfl
      rw [heq2, h.deriv]
    rw [hderiv]
    have hfa_le : |dfa a s| ≤ |df s| := hdfale a s hs1
    rw [abs_mul, abs_mul, abs_inv, abs_of_nonneg (sub_nonneg.mpr hF.le)]
    have hstep : |dfa a s| * (|df s|⁻¹ * (β l - α l))
        ≤ |df s| * (|df s|⁻¹ * (β l - α l)) := by
      refine mul_le_mul_of_nonneg_right hfa_le ?_
      exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (sub_nonneg.mpr hF.le)
    have hcancel : |df s| * (|df s|⁻¹ * (β l - α l)) = β l - α l := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hf'_pos), one_mul]
    have hβmα1 : β l - α l ≤ 1 := by linarith [hF.le_one, hF.nonneg]
    linarith
  · -- degenerate case: the composite is constant
    have heq : α l = β l := le_antisymm hF.le (le_of_not_gt hlt)
    have hfs : f (Fin.snoc l s) = α l := by
      have h1 := (hF.bound s hs1).1
      have h2 := (hF.bound s hs1).2
      exact le_antisymm (by rw [heq]; exact h2) h1
    have hev : (fun τ' : ℝ => fa a (chartVal g α β l (fun _ => τ')))
        =ᶠ[𝓝 τ] (fun _ => fa a s) := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with τ' hτ'
      have hzero : α l + τ' * (β l - α l) = α l := by rw [heq]; ring
      have hgv' : g (Fin.snoc l (α l + τ' * (β l - α l))) = s :=
        hF.inv_eq (α l + τ' * (β l - α l)) s
          (by rw [mem_invSet]; exact ⟨hs1, by rw [hzero]; exact hfs⟩)
      show fa a (g (Fin.snoc l (α l + τ' * (β l - α l)))) = fa a s
      rw [hgv']
    refine ⟨DifferentiableAt.congr_of_eventuallyEq (differentiableAt_const (fa a s)) hev, ?_⟩
    rw [hev.deriv_eq, deriv_const]
    simp

end Work.WilkG4c
