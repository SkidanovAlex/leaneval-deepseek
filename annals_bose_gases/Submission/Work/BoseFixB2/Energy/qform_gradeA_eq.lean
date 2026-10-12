import ChallengeDeps
import Submission.Work.BoseFixB2.Energy.normSq_gradePsi
import Submission.Work.BoseFixB2.Energy.qform_eq_double_sum
import Submission.Work.BoseFixB2.Energy.term_ij
import Submission.Work.BoseFixB2.Energy.wordB_sum_secProj
import Submission.Work.BoseFixB2.Pot.potWordU_integrable
import Submission.Work.BoseFixB2.Sector.secProj_resolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.qform_gradeA_eq` — FS §6's energy identity `⟨ψ, 𝒜ψ⟩‖Ψ‖² = ⟨Ψ, HΨ⟩`

FS `lem:LocMatrices` (`final_v2.tex` ll. 1365–1445) grades a box state `Ψ` by the spectrum of
the excitation-number operator `n₊ = ΣᵢQᵢ`, forms the matrix
`𝒜_{ij} = ‖1_iΨ‖⁻¹‖1_jΨ‖⁻¹⟨1_iΨ, H_Λ1_jΨ⟩` and the norm profile `ψ_i = ‖1_iΨ‖/‖Ψ‖`, and uses
the identity

    ⟨ψ, 𝒜ψ⟩·‖Ψ‖² = ⟨Ψ, H_ΛΨ⟩   (i.e. `qform A ψ ψ * normB Φ = wordB Φ`)

as the equation that ties the quadratic form of Lieb–Solovej's localisation theorem to the
physical energy of the box.

In the corpus vocabulary (`Submission.Work.BoseFixB2.Defs`):

* `A = gradeA v h μ n (fsSide v μ) Φ`, `ψ = gradePsi v h μ n (fsSide v μ) Φ`, built from the
  sectors `secProj (fsSide v μ) k Φ` of `Φ` (padded by `vecZ` over the window
  `iRange (fsNn v μ n)`);
* `normB v μ n Φ = ∫_{abox n ℓ} Φ²` and `wordB v h μ n Φ = boxFormB … Φ`, the box-restricted form
  (FS's `H_Λ(μ)`), with `ℓ = fsSide v μ` and the parameters `paramsAt μ (a v)`.

## The proof

1. **The matrix elements.**  For sector indices `i, j ∈ [0,n]` the sandwiched entry is
   `star ψ_i · 𝒜_{ij} · ψ_j = polB (vecZ i) (vecZ j) / normB Φ` (`Energy.term_ij`): the two
   profile factors `√‖1_iΦ‖/√‖Φ‖` cancel the normalisation `√‖1_iΦ‖√‖1_jΦ‖` of `𝒜_{ij}`; when
   one of the two sector norms vanishes, `𝒜_{ij}` vanishes by its defining guard while `polB` of
   that sector vanishes too (the sector then vanishes on the box, and `wordB` is box-local).
2. **The index range.**  `Energy.qform_eq_double_sum` restricts the window sum
   `qform … (iRange (fsNn v μ n))` to the sector range `[0,n]²` (the profile vanishes outside
   `[0,n]`, and so does `gradeA`'s guard).
3. **The polarisation.**  `Σ_{k,l ≤ n} polB (1_kΦ) (1_lΦ) = wordB Φ`
   (`sum_polB_vecZ_eq_wordB` below): with all coefficients equal to `1` this is the polarisation
   identity of the box word along its sectors, i.e. `Energy.wordB_sum_secProj` at `c ≡ 1`,
   combined with the resolution of the identity `Σ_{k ≤ n} 1_{n₊=k}Φ = Φ`
   (`Sector.secProj_resolution`), followed by the reindexing `Σ_{i ∈ [0,n]} ↦ Σ_{k ≤ n}` of the
   `ℤ`-grading (`sum_Icc_zero_cast_eq_sum_range`, `vecZ_apply`).
4. Multiply by `normB Φ ≠ 0` (`hpos`).  The degenerate box side `ℓ ≤ 0` — outside the range of
   `hpos` for `n ≥ 1`, but not for `n = 0` — is handled separately: then `wordB ≡ 0`
   (`Polar.boxFormB_eq_zero_of_nonpos`), hence `polB ≡ 0` and `gradeA ≡ 0`, so both sides of the
   identity vanish.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2.Energy

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option linter.unusedVariables false

/-- The polarised box word in explicit form (definitional unfolding of `polB`), kept as a named
rewrite so that `polB` can be normalised away in the algebraic steps. -/
private lemma polB_apply {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} (X Y : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB2.polB v h μ n X Y
      = (Work.BoseBoxFix.wordB v h μ n (fun x => X x + Y x)
          - Work.BoseBoxFix.wordB v h μ n (fun x => X x - Y x)) / 4 := rfl

/-- **The polarisation of the box word along its sectors:**

    `Σ_{k,l ≤ n} polB (1_{n₊=k}Φ) (1_{n₊=l}Φ) = wordB Φ`.

This is `Energy.wordB_sum_secProj` with all coefficients equal to `1`, together with the
resolution of the identity `Σ_{k ≤ n} 1_{n₊=k}Φ = Φ` (`Sector.secProj_resolution`) applied to the
argument of `wordB`. -/
private lemma sum_polB_sec_eq_wordB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < Work.BoseFixB2.fsSide v μ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
        (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))
      = Work.BoseBoxFix.wordB v h μ n Φ := by
  -- the resolution of the identity, as an identity of functions
  have hfun : (fun x : Submission.BoseGases.X n =>
        ∑ k ∈ Finset.range (n + 1), (1 : ℝ) *
          Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x) = Φ := by
    funext x
    rw [show (∑ k ∈ Finset.range (n + 1), (1 : ℝ) *
          Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x)
        = (∑ k ∈ Finset.range (n + 1),
            Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) x from by
          rw [Finset.sum_apply]; simp]
    rw [Work.BoseFixB2.Sector.secProj_resolution hℓ hΦ.continuous]
  have h := wordB_sum_secProj (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hΦ hw (fun _ => 1)
  rw [hfun] at h
  simpa using h.symm

/-- **The polarisation identity in the `ℤ`-indexed sector range.**  Reindexing `Σ_{i ∈ [0,n]}` to
`Σ_{k ≤ n}` (`sum_Icc_zero_cast_eq_sum_range`) and unfolding `vecZ` on the sector range
(`vecZ_apply`) turns the previous statement into the form in which the matrix elements of
`gradeA` produce it. -/
private lemma sum_polB_vecZ_eq_wordB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < Work.BoseFixB2.fsSide v μ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
        (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) :
    (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
        Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
          (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j))
      = Work.BoseBoxFix.wordB v h μ n Φ := by
  trans (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))
  · rw [sum_Icc_zero_cast_eq_sum_range
      (fun i : ℤ => ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
        Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
          (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)) n]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [sum_Icc_zero_cast_eq_sum_range
      (fun j : ℤ => Work.BoseFixB2.polB v h μ n
        (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ))
        (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)) n]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hk' : (k : ℤ) ≤ (n : ℤ) := by
      rw [Finset.mem_range] at hk; exact_mod_cast Nat.lt_succ_iff.mp hk
    have hl' : (l : ℤ) ≤ (n : ℤ) := by
      rw [Finset.mem_range] at hl; exact_mod_cast Nat.lt_succ_iff.mp hl
    rw [Work.BoseFixB2.DvApriori.vecZ_apply (ℓ := Work.BoseFixB2.fsSide v μ) (i := (k : ℤ))
        (Int.natCast_nonneg k) hk',
      Work.BoseFixB2.DvApriori.vecZ_apply (ℓ := Work.BoseFixB2.fsSide v μ) (i := (l : ℤ))
        (Int.natCast_nonneg l) hl',
      Int.toNat_natCast, Int.toNat_natCast]
  · exact sum_polB_sec_eq_wordB hℓ hΦ hw

theorem qform_gradeA_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ) : Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) * Work.BoseBoxFix.normB v μ n Φ = Work.BoseBoxFix.wordB v h μ n Φ := by
  by_cases hℓ : 0 < Work.BoseFixB2.fsSide v μ
  · -- the box side is positive: the identity is the polarisation of `wordB` along the sectors
    have hw := Work.BoseFixB2.Pot.potWordU_integrable (v := v) (h := h) (μ := μ) (n := n)
      hR hv_supp hv1 (Work.BoseFixB2.fsSide v μ)
    -- (1) the matrix elements of `gradeA` against the profile
    have hterm : (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
        star (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ i)
          * Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j
          * Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j)
        = (((∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
              (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j))
            / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) := by
      rw [show (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            star (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ i)
              * Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j
              * Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j)
          = ∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
              ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
                (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)
                / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) from
        Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj =>
          term_ij (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hpos hΦ hi hj))]
      have h1 : (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
              (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)
              / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ))
          = (((∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
              Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
                (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)
              / Work.BoseBoxFix.normB v μ n Φ : ℝ)) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl (fun i _ => (Complex.ofReal_sum _ _).symm)
      have h2 : (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
              Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
                (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)
              / Work.BoseBoxFix.normB v μ n Φ : ℝ)
          = (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
              Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
                (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j))
            / Work.BoseBoxFix.normB v μ n Φ := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => (Finset.sum_div _ _ _).symm)
      rw [h1, h2]
    -- (2) the polarisation of `wordB` along the sectors
    have hpol := sum_polB_vecZ_eq_wordB (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ)
      hℓ hΦ hw
    -- (3) the index range, and the multiplication by `normB Φ ≠ 0`
    rw [qform_eq_double_sum (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ), hterm]
    rw [Complex.ofReal_re, hpol, div_mul_cancel₀ _ (ne_of_gt hpos)]
  · -- a nonpositive box side: `wordB` vanishes identically, hence so does `polB`
    have hle : Work.BoseFixB2.fsSide v μ ≤ 0 := le_of_not_gt hℓ
    have hQ : ∀ X : Submission.BoseGases.X n → ℝ, Work.BoseBoxFix.wordB v h μ n X = 0 := by
      intro X
      simpa only [Work.BoseBoxFix.wordB, Work.BoseFixB2.fsSide] using
        (Work.BoseFixB2.Polar.boxFormB_eq_zero_of_nonpos (v := v) (g := Submission.BoseGases.g0 v h)
          (ℓ := Work.BoseFixB2.fsSide v μ) (μ := μ)
          (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          (εT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b) hle X)
    have hA : ∀ i j : ℤ, Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j = 0 := by
      intro i j
      rw [Work.BoseFixB2.gradeA]
      by_cases hc : (0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
          ∧ 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
          ∧ 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j))
      · rw [if_pos hc]
        have hp : Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ i)
            (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j) = 0 := by
          rw [Work.BoseFixB2.polB, hQ, hQ, sub_self, zero_div]
        rw [hp]
        simp
      · rw [if_neg hc]
    rw [Work.UBBInputs3.qform]
    simp [hA, hQ]

end Work.BoseFixB2.Energy
