import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceTransport
import Submission.Work.MB.exists_realFock_eq_sliceF_re_im_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.sliceModelWindow_deg_ae` — the weak-class `ExcWindow` of the selected slice

The **measurable/bounded** ("weak") twin of `Work.BoseBoxFock.sliceModelWindow_deg`
(`Submission/Work/BoseBoxFock/sliceTransport.lean`): if the slice `sliceF e S Φ y` has no *bad*
monomial coefficient (`hG`), then it is the sum of the realisations of two *real* model vectors
`Ψ₁ Ψ₂`, **both** of which lie in the excited window `ExcWindow M n` **and** are *homogeneous of
degree* `S.card`.

The strong chain assumes the modes be `Continuous` with `HasCompactSupport` and the state be
`Continuous` with `HasCompactSupport`; those hypotheses are *unsatisfiable* at the honest modes of
the box ↔ model bridge (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`), so the selection chain
has to be re-run in the honest class

* `Measurable (e l)`, `∃ C, ∀ x, ‖e l x‖ ≤ C`, `Function.support (e l) ⊆ boxL ℓ`,
* `Measurable Φ`, `∃ C, ∀ x, ‖Φ x‖ ≤ C`, `Function.support Φ ⊆ boxPow n ℓ`.

Every ingredient of the strong proof is available in that class, verbatim:

* the slice is *symmetric* in its `S.card` slots — `Work.MB.sliceF_symm_weak`;
* the slice lies in the `ℂ`-span of the mode monomials — `Work.MB.sliceF_mem_monSpan_weak`;
* a *symmetric* element of that span is the `boxRealiseC`-realisation of a complexified Fock vector
  — `Work.BoseBoxFock.symm_mem_span_range_boxRealiseC` (hypothesis free);

so the weak `boxRealiseC`-realisation of the slice is produced exactly as in
`exists_realFock_eq_sliceF_re_im_ae`, and the rest of the argument
(`boxRealiseC_filter` + `sliceWindow_of_coeff_zero`, which already asks only for orthonormality,
`MemLp ⊤` and box support, never for continuity) is the strong proof line by line.
-/

namespace Work.MB

theorem sliceModelWindow_deg_ae {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow n ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3))
    (hG : ∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
      ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α)
        (Work.BoseBoxFock.sliceF e S Φ y) = 0) :
    ∃ Ψ₁ Ψ₂ : Work.BoseB4.RealFock m,
      Work.BoseDict.boxRealise e S.card Ψ₁
        + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂
        = Work.BoseBoxFock.sliceF e S Φ y ∧
      Work.BoseBoxFock.ExcWindow M n Ψ₁ ∧ Work.BoseBoxFock.ExcWindow M n Ψ₂ ∧
      (∀ α ∈ Ψ₁.support, α.sum (fun _ k => k) = S.card) ∧
      (∀ α ∈ Ψ₂.support, α.sum (fun _ k => k) = S.card) := by
  classical
  -- **(0)** the slice is the `boxRealiseC`-realisation of a complexified Fock vector (weak class)
  obtain ⟨Ψc, hΨc⟩ : ∃ Ψc : Work.BoseBoxFock.CFock m,
      Work.BoseBoxFock.boxRealiseC e S.card Ψc = Work.BoseBoxFock.sliceF e S Φ y :=
    Work.BoseBoxFock.symm_mem_span_range_boxRealiseC e
      (sliceF_symm_weak e hmeas hbdE hsupp S Φ hΦm hΦb hΦsym y)
      (sliceF_mem_monSpan_weak e hmeas hbdE hsupp S Φ hΦm hΦb y)
  -- **(1)** throw away the multi-indices of degree `≠ S.card`
  set Ψc' : Work.BoseBoxFock.CFock m :=
    Ψc.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = S.card) with hΨc'def
  have hdeg : ∀ α ∈ Ψc'.support, α.sum (fun _ k => k) = S.card := by
    intro α hα
    rw [hΨc'def, Finsupp.support_filter] at hα
    exact (Finset.mem_filter.mp hα).2
  have hreal : Work.BoseBoxFock.boxRealiseC e S.card Ψc' = Work.BoseBoxFock.sliceF e S Φ y := by
    rw [hΨc'def]
    exact (Work.BoseBoxFock.boxRealiseC_filter e Ψc).trans hΨc
  -- **(2)** the coefficient condition kills every bad monomial
  have hwin : ∀ α ∈ Ψc'.support, ((S.card - α 0 : ℕ) : ℝ) ≤ (⌊M⌋₊ : ℝ) :=
    Work.BoseBoxFock.sliceWindow_of_coeff_zero (ℓ := ℓ) (M := M) e horth hbdd hsupp Ψc'
      (Work.BoseBoxFock.sliceF e S Φ y) hreal hdeg hG
  -- **(3)** the two branches of the complexified vector
  have hsub : ∀ Ψ : Work.BoseB4.RealFock m, Ψ = Work.BoseBoxFock.realPart Ψc'
      ∨ Ψ = Work.BoseBoxFock.imagPart Ψc' → Ψ.support ⊆ Ψc'.support := by
    intro Ψ hΨ
    rcases hΨ with h | h
    · rw [h]; exact Finsupp.support_mapRange
    · rw [h]; exact Finsupp.support_mapRange
  have hbranch : ∀ Ψ : Work.BoseB4.RealFock m, Ψ = Work.BoseBoxFock.realPart Ψc'
      ∨ Ψ = Work.BoseBoxFock.imagPart Ψc' → Work.BoseBoxFock.ExcWindow M n Ψ := by
    intro Ψ hΨ
    rw [Work.BoseBoxFock.excwindow_iff]
    refine ⟨fun α hα => ?_, fun α hα => ?_⟩
    · have hd := hdeg α (hsub Ψ hΨ hα)
      calc Work.BoseBoxFock.deg α = α.sum (fun _ k => k) := rfl
        _ = S.card := hd
        _ ≤ n := by simpa using Finset.card_le_univ S
    · have hd := hdeg α (hsub Ψ hΨ hα)
      have h1 := hwin α (hsub Ψ hΨ hα)
      have h2 : S.card - α 0 ≤ ⌊M⌋₊ := Nat.cast_le.mp h1
      have h3 : S.card ≤ ⌊M⌋₊ + α 0 := Nat.sub_le_iff_le_add.mp h2
      calc Work.BoseBoxFock.deg α = α.sum (fun _ k => k) := rfl
        _ = S.card := hd
        _ ≤ ⌊M⌋₊ + α 0 := h3
  refine ⟨Work.BoseBoxFock.realPart Ψc', Work.BoseBoxFock.imagPart Ψc', ?_,
    hbranch _ (Or.inl rfl), hbranch _ (Or.inr rfl),
    fun α hα => hdeg α (hsub _ (Or.inl rfl) hα),
    fun α hα => hdeg α (hsub _ (Or.inr rfl) hα)⟩
  rw [← Work.BoseBoxFock.boxRealiseC_eq_re_add_im e Ψc']
  exact hreal

end Work.MB
