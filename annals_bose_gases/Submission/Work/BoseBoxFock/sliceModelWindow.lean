import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceWindow_of_coeff_zero
import Submission.Work.BoseBoxFock.window_ops
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceModelWindow` — the `ExcWindow` of the selected slice

Step 6 of the BF3c pipeline, final assembly (`FINDING_BF3c_selection_s9.md` §2 (B)): if the slice
`sliceF e S Φ y` has no *bad* monomial coefficient (`hG`: the `cIPn`-coefficient of `M_α` vanishes
whenever `S.card − α 0 > ⌊M⌋₊`), then it is the realisation of **two real model vectors** — the two
branches `realPart`, `imagPart` of the complexified model vector — and **both** of them lie in the
excited window `ExcWindow M n`.

The two ingredients are `exists_boxRealiseC_eq_sliceF` (the slice is `boxRealiseC` of a `CFock`
vector) and `sliceWindow_of_coeff_zero` (the coefficient condition forces the support into the
window).  Because `boxRealiseC` ignores the multi-indices of degree `≠ S.card`, the `CFock` vector
is first replaced by its degree-`S.card` part (`Finsupp.filter`, `boxRealiseC_filter`), which is
what makes `hdeg` of `sliceWindow_of_coeff_zero` available and gives `deg α = S.card ≤ n`.

`ExcWindow` for the two branches is exactly the `excwindow_iff` coordinate condition; the branch
supports are contained in `supp Ψc'` (`Finsupp.support_mapRange`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The realisation only sees the degree-`d` part.**  `boxRealiseC e d` kills every multi-index
whose total degree is not `d`, so filtering a `CFock` vector to the degree-`d` multi-indices does
not change its realisation. -/
lemma boxRealiseC_filter {m d : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (Ψ : CFock m) :
    boxRealiseC e d (Ψ.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = d))
      = boxRealiseC e d Ψ := by
  have hsplit : Ψ = Ψ.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = d)
      + Ψ.filter (fun α : Fin m →₀ ℕ => ¬ (α.sum (fun _ k => k) = d)) := by
    ext α
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases h : α.sum (fun _ k => k) = d <;> simp [h]
  have hkill : boxRealiseC e d
      (Ψ.filter (fun α : Fin m →₀ ℕ => ¬ (α.sum (fun _ k => k) = d))) = 0 := by
    rw [boxRealiseC, Finsupp.lsum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun α hα => ?_
    have hmem : ¬ (α.sum (fun _ k => k) = d) := (Finset.mem_filter.mp hα).2
    rw [if_neg hmem]
    rfl
  calc boxRealiseC e d (Ψ.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = d))
      = boxRealiseC e d (Ψ.filter (fun α : Fin m →₀ ℕ => ¬ (α.sum (fun _ k => k) = d)))
        + boxRealiseC e d (Ψ.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = d)) := by
        rw [hkill, zero_add]
    _ = boxRealiseC e d (Ψ.filter (fun α : Fin m →₀ ℕ => ¬ (α.sum (fun _ k => k) = d))
          + Ψ.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = d)) :=
        (map_add (boxRealiseC e d) _ _).symm
    _ = boxRealiseC e d Ψ := by rw [add_comm, ← hsplit]

/-- **The two real model vectors of the selected slice, with the excited window.**

If the slice `sliceF e S Φ y` has no bad monomial coefficient (`hG`), then it is the sum of the
realisations of two *real* model vectors, and both of them lie in `ExcWindow M n`. -/
theorem sliceModelWindow {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (e : Fin m → Ω → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n), (fun x : Fin n → Ω => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → Ω)
    (hG : ∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
      ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α) (sliceF e S Φ y) = 0) :
    ∃ Ψ₁ Ψ₂ : Work.BoseB4.RealFock m,
      Work.BoseDict.boxRealise e S.card Ψ₁ + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂
        = sliceF e S Φ y ∧
      ExcWindow M n Ψ₁ ∧ ExcWindow M n Ψ₂ := by
  classical
  obtain ⟨Ψc, hΨc⟩ := exists_boxRealiseC_eq_sliceF e hcont hcomp S Φ hΦ hΦc hΦsym y
  set Ψc' : CFock m := Ψc.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = S.card)
    with hΨc'def
  have hdeg : ∀ α ∈ Ψc'.support, α.sum (fun _ k => k) = S.card := by
    intro α hα
    rw [hΨc'def, Finsupp.support_filter] at hα
    exact (Finset.mem_filter.mp hα).2
  have hreal : boxRealiseC e S.card Ψc' = sliceF e S Φ y := by
    rw [hΨc'def]
    exact (boxRealiseC_filter e Ψc).trans hΨc
  have hwin : ∀ α ∈ Ψc'.support, ((S.card - α 0 : ℕ) : ℝ) ≤ (⌊M⌋₊ : ℝ) :=
    sliceWindow_of_coeff_zero (ℓ := ℓ) (M := M) e horth hbdd hsupp Ψc' (sliceF e S Φ y)
      hreal hdeg hG
  -- the coordinate form of the window for the two branches
  have hbranch : ∀ Ψ : Work.BoseB4.RealFock m, Ψ = realPart Ψc' ∨ Ψ = imagPart Ψc' →
      ExcWindow M n Ψ := by
    intro Ψ hΨ
    rw [excwindow_iff]
    have hsub : Ψ.support ⊆ Ψc'.support := by
      rcases hΨ with h | h
      · rw [h]
        exact Finsupp.support_mapRange
      · rw [h]
        exact Finsupp.support_mapRange
    refine ⟨fun α hα => ?_, fun α hα => ?_⟩
    · have hd := hdeg α (hsub hα)
      calc deg α = α.sum (fun _ k => k) := rfl
        _ = S.card := hd
        _ ≤ n := by simpa using Finset.card_le_univ S
    · have hd := hdeg α (hsub hα)
      have h1 := hwin α (hsub hα)
      have h2 : S.card - α 0 ≤ ⌊M⌋₊ := Nat.cast_le.mp h1
      have h3 : S.card ≤ ⌊M⌋₊ + α 0 := Nat.sub_le_iff_le_add.mp h2
      calc deg α = α.sum (fun _ k => k) := rfl
        _ = S.card := hd
        _ ≤ ⌊M⌋₊ + α 0 := h3
  refine ⟨realPart Ψc', imagPart Ψc', ?_, hbranch _ (Or.inl rfl), hbranch _ (Or.inr rfl)⟩
  rw [← boxRealiseC_eq_re_add_im e Ψc']
  exact hreal

end Work.BoseBoxFock
