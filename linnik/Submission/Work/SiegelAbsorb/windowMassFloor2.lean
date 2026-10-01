import Mathlib
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.SiegelBase

namespace Work.SiegelAbsorb

/-- **Per-height-window Abel summation with a repulsion floor, split at `θ·𝓛`.**

Let `S` be a finite set of zero-pairs of level `q > 1`, all of height `|Im ρ|·𝓛 ≤ H·𝓛`, none of them
the exceptional pair, and every member with `λ(ρ) ≥ Λ`.  Suppose the `λ₁`-free log-free count at
height `H` is available in two ranges:

* `pairCountHeight χ₁ β₁ t (H·𝓛) ≤ C₂·e^{(5/2)t}·H^{3/2}` for `0 < t ≤ θ·𝓛`,
* `pairCountHeight χ₁ β₁ t (H·𝓛) ≤ C₃·e^{(9/2)t}·H^{3/2}` for `0 < t ≤ 𝓛`.

Then the window mass is at most the sum of the two layer-cake bounds: the part of `S` with
`λ(ρ) ≤ θ·𝓛` is handled by the first count (geometric ratio `e^{5/2 - 49/10} = e^{-12/5}`), and the
part with `λ(ρ) > θ·𝓛` by the second (geometric ratio `e^{9/2 - 49/10} = e^{-2/5}`), whose Abel
constant `θ·𝓛` produces the factor `e^{-(2/5)·θ𝓛}`. -/
lemma windowMassFloor2 {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ C₃ H Λ θ : ℝ} (hC₂ : 0 < C₂) (hC₃ : 0 < C₃) (hH : 0 < H) (hΛ : 0 < Λ) (hθ : 0 < θ)
    (hcnt₁ : ∀ t : ℝ, 0 < t → t ≤ θ * Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    (hcnt₂ : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ))
    (hfloor : ∀ z ∈ S, Λ ≤ Work.LinnikContract.lamOf q z.2) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * Real.exp (-(12 / 5) * Λ)
            / (1 - Real.exp (-(12 / 5)))
        + C₃ * H ^ (3 / 2 : ℝ) * Real.exp (9 / 2) * Real.exp (-(2 / 5) * (θ * Real.log (q : ℝ)))
            / (1 - Real.exp (-(2 / 5))) := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  -- the splitting height
  set t₀ : ℝ := θ * Real.log (q : ℝ) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; exact mul_pos hθ hlog
  -- every zero counted in the window has `λ(ρ) ≤ 𝓛`
  have hlamL : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ Real.log (q : ℝ) := by
    intro z hz
    have h1 : 0 < z.2.re := Work.LinnikAreas.zeroMult_re_pos z.1 (hzm z hz)
    rw [Work.LinnikContract.lamOf]
    calc (1 - z.2.re) * Real.log (q : ℝ) ≤ 1 * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlog.le
      _ = Real.log (q : ℝ) := by ring
  -- the counting function at a cut-off `t ≤ θ·𝓛`, in the shape consumed by the layer-cake theorem
  have hcnt₁' : ∀ t : ℝ, 0 < t → t ≤ θ * Real.log (q : ℝ) →
      (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp ((5 / 2) * t) := by
    intro t htpos htθ
    have hdom := Work.LinnikAreas.pairCountHeight_dom hq χ₁ β₁
      (S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
    calc (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) := hdom
      _ ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := hcnt₁ t htpos htθ
      _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp ((5 / 2) * t) := by ring
  -- the counting function at a cut-off `t ≤ 𝓛`
  have hcnt₂' : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ C₃ * H ^ (3 / 2 : ℝ) * Real.exp ((9 / 2) * t) := by
    intro t htpos htL
    have hdom := Work.LinnikAreas.pairCountHeight_dom hq χ₁ β₁
      (S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
    calc (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) := hdom
      _ ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ) := hcnt₂ t htpos htL
      _ = C₃ * H ^ (3 / 2 : ℝ) * Real.exp ((9 / 2) * t) := by ring
  -- the low part: `λ(ρ) ≤ θ·𝓛`
  have h1 : (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t₀),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * Real.exp (-(12 / 5) * Λ)
          / (1 - Real.exp (-(12 / 5))) := by
    have h := Work.LinnikAreas.sum_mul_exp_neg_le_of_count
      (S := S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t₀))
      (m := fun z : DirichletCharacter ℂ q × ℂ => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      (lam := fun z : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q z.2)
      (a₀ := 49 / 10) (Λ := Λ) (L := t₀) (D := C₂) (lam₁ := H ^ (3 / 2 : ℝ)) (c := 5 / 2)
      (by norm_num) (by norm_num) (by norm_num) hC₂ hΛ (Real.rpow_pos_of_pos hH _)
      (fun z _ => Nat.cast_nonneg _)
      (fun z hz => hfloor z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun t htΛ htL => by
        have htpos : 0 < t := lt_of_lt_of_le hΛ htΛ
        have htθ : t ≤ θ * Real.log (q : ℝ) := le_trans htL (le_of_eq ht₀)
        have hfil : (S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t₀)).filter
              (fun z => Work.LinnikContract.lamOf q z.2 ≤ t)
            = S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t) := by
          ext z
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hzS, _⟩, hzt⟩; exact ⟨hzS, hzt⟩
          · rintro ⟨hzS, hzt⟩; exact ⟨⟨hzS, le_trans hzt htL⟩, hzt⟩
        rw [hfil]
        exact hcnt₁' t htpos htθ)
    rwa [show (5 / 2 - 49 / 10 : ℝ) = -(12 / 5) by norm_num] at h
  -- the high part: `θ·𝓛 < λ(ρ)`
  have h2 : (∑ z ∈ S.filter (fun z => ¬ (Work.LinnikContract.lamOf q z.2 ≤ t₀)),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₃ * H ^ (3 / 2 : ℝ) * Real.exp (9 / 2)
          * Real.exp (-(2 / 5) * (θ * Real.log (q : ℝ)))
          / (1 - Real.exp (-(2 / 5))) := by
    have h := Work.LinnikAreas.sum_mul_exp_neg_le_of_count
      (S := S.filter (fun z => ¬ (Work.LinnikContract.lamOf q z.2 ≤ t₀)))
      (m := fun z : DirichletCharacter ℂ q × ℂ => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
      (lam := fun z : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q z.2)
      (a₀ := 49 / 10) (Λ := t₀) (L := Real.log (q : ℝ)) (D := C₃)
      (lam₁ := H ^ (3 / 2 : ℝ)) (c := 9 / 2)
      (by norm_num) (by norm_num) (by norm_num) hC₃ ht₀pos (Real.rpow_pos_of_pos hH _)
      (fun z _ => Nat.cast_nonneg _)
      (fun z hz => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hz).2))
      (fun z hz => hlamL z (Finset.mem_filter.mp hz).1)
      (fun t htΛ htL => by
        have htpos : 0 < t := lt_of_lt_of_le ht₀pos htΛ
        have hsub : ((S.filter (fun z => ¬ (Work.LinnikContract.lamOf q z.2 ≤ t₀))).filter
              (fun z => Work.LinnikContract.lamOf q z.2 ≤ t))
            ⊆ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t) := by
          intro z hz
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1,
              (Finset.mem_filter.mp hz).2⟩
        have hle := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun z : DirichletCharacter ℂ q × ℂ => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
          hsub (fun z _ _ => Nat.cast_nonneg _)
        exact le_trans hle (hcnt₂' t htpos htL))
    rw [show (9 / 2 - 49 / 10 : ℝ) = -(2 / 5) by norm_num, ht₀] at h
    exact h
  -- assemble the two parts
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := S)
    (p := fun z : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q z.2 ≤ t₀)
    (f := fun z : DirichletCharacter ℂ q × ℂ => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
      * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
  rw [← hsplit]
  exact add_le_add h1 h2

end Work.SiegelAbsorb
