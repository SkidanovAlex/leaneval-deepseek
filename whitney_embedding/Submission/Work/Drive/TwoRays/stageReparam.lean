import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Routing.compImmersion

/-!
# The stage reparametrisation of the `TwoLanes` recursion

The glued piece of a stage (`Work.Noncompact.CompressionTube.exists_gluedPiece`) lives on the
parameter interval `[0, L+1]`: a straight spike `t ↦ c.symm (c σ + t • u)` for `t ∈ [0,L]` followed by
the mid arc.  To feed it into the state of the next stage (`Work.Noncompact.CompressionTube.StageState`)
one must reparametrise it to `[0,1]`, and the *initial germ* must come out in the **same chart and the
same direction** `u` as the arriving piece's terminal germ (that is the junction row `Lane.hgerm`,
and `StageState.germ_pair` reads it off `T.cin = S.cout`, `T.uin = S.uout`).

The naive affine reparametrisation `t ↦ (L+1) * t` (used by
`Work.Noncompact.CompressionTube.exists_reparametrized_piece`) gives the germ
`c.symm (c σ + t • ((L+1) • u))` — *direction* `(L+1) • u`, which does **not** match `S.uout = u`.
This file supplies the reparametrisation that does match: a smooth strictly increasing `χ` with
`χ t = t` for `t ≤ δ` (so the initial germ survives verbatim), `χ t = t + L` for `t ≥ 1 - δ'` (so the
terminal germ survives as a straight germ), `χ 1 = L + 1` and `χ '' [0,1] ⊆ [0, L+1]`.

The transfer lemmas for such a `χ` are already PROVED in
`Work.Noncompact.Routing.reparamTransport` (`contMDiff_comp_reparam`,
`injective_mfderiv_comp_reparam`, `injOn_comp_reparam`, `germ_comp_reparam`); what was missing is
`χ` itself. -/

namespace Work.Drive.TwoRays

open Set
open scoped Manifold ContDiff

/-- **The stage reparametrisation.**  For `L > 0`, `δ > 0`, `δ' > 0`, `δ + δ' < 1` there is a smooth
strictly increasing `χ : ℝ → ℝ` with `χ t = t` for `t ≤ δ`, `χ t = t + L` for `t ≥ 1 - δ'`,
`χ 1 = L + 1`, `0 < deriv χ t` for all `t`, and `χ '' Set.Icc 0 1 ⊆ Set.Icc 0 (L+1)`.

It is `χ t = t + L * Real.smoothTransition ((t - δ)/(1 - δ' - δ))`. -/
theorem exists_stageReparam {L δ δ' : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδδ' : δ + δ' < 1) :
    ∃ χ : ℝ → ℝ, ContMDiff Work.Noncompact.CompressionTube.MCreal
        Work.Noncompact.CompressionTube.MCreal
        Work.Noncompact.CompressionTube.smoothOrder χ ∧
      (∀ t : ℝ, t ≤ δ → χ t = t) ∧
      (∀ t : ℝ, 1 - δ' ≤ t → χ t = t + L) ∧
      (∀ t : ℝ, 0 < deriv χ t) ∧
      χ 1 = L + 1 ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → χ t ∈ Set.Icc (0:ℝ) (L + 1)) := by
  set w : ℝ := 1 - δ' - δ with hwdef
  have hw : 0 < w := by rw [hwdef]; linarith
  have hwne : w ≠ 0 := ne_of_gt hw
  set φ : ℝ → ℝ := fun t => Real.smoothTransition ((t - δ) / w) with hφdef
  set χ : ℝ → ℝ := fun t => t + L * φ t with hχdef
  have hφcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
    rw [hφdef]
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const w)
  have hφmono : Monotone φ := by
    rw [hφdef]
    refine Real.smoothTransition.monotone.comp ?_
    intro a b hab
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  have hχcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]
    exact contDiff_id.add (contDiff_const.mul hφcd)
  have hzero : ∀ t : ℝ, t ≤ δ → φ t = 0 := by
    intro t ht
    rw [hφdef]
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)
  have hone : ∀ t : ℝ, 1 - δ' ≤ t → φ t = 1 := by
    intro t ht
    rw [hφdef]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hw]
    rw [hwdef] at *
    linarith
  have hderiv : ∀ t : ℝ, deriv χ t = 1 + L * deriv φ t := by
    intro t
    rw [hχdef]
    have hφhat : HasDerivAt φ (deriv φ t) t :=
      (hφcd.hasStrictDerivAt (by simp)).hasDerivAt
    have hhat : HasDerivAt (fun s : ℝ => s + L * φ s) (1 + L * deriv φ t) t :=
      (hasDerivAt_id t).add (hφhat.const_mul L)
    exact hhat.deriv
  refine ⟨χ, hχcd.contMDiff, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    show t + L * φ t = t
    rw [hzero t ht]
    ring
  · intro t ht
    show t + L * φ t = t + L
    rw [hone t ht]
    ring
  · intro t
    have hder : deriv (fun s : ℝ => s + L * φ s) t = 1 + L * deriv φ t := by
      have hφhat : HasDerivAt φ (deriv φ t) t := (hφcd.hasStrictDerivAt (by simp)).hasDerivAt
      exact ((hasDerivAt_id t).add (hφhat.const_mul L)).deriv
    have h1 : 0 ≤ deriv φ t := hφmono.deriv_nonneg
    have h2 : 0 < 1 + L * deriv φ t := by nlinarith [hL, h1]
    simpa [hχdef, hder] using h2
  · show (1 : ℝ) + L * φ 1 = L + 1
    rw [hone 1 (by linarith)]
    ring
  · intro t ht
    have hφnn : 0 ≤ φ t := by
      rw [hφdef]
      exact Real.smoothTransition.nonneg _
    have hφle : φ t ≤ 1 := by
      rw [hφdef]
      exact Real.smoothTransition.le_one _
    show t + L * φ t ∈ Set.Icc (0:ℝ) (L + 1)
    constructor
    · have h2 : 0 ≤ L * φ t := mul_nonneg hL.le hφnn
      linarith [ht.1]
    · have h2 : L * φ t ≤ L := by
        have h3 := mul_le_mul_of_nonneg_left hφle hL.le
        rwa [mul_one] at h3
      linarith [ht.2]

/-! ## The transfer to the piece -/

/-- **Immersion transports through a reparametrisation with non-zero derivative, at a point.**
`Work.Routing.injective_mfderiv_comp_of_deriv_ne_zero` with the immersion hypothesis at the single
parameter `θ t` (which is what the stage engine has: its piece is an immersion only on `[0, L+1]`). -/
theorem injective_mfderiv_comp_reparam_at {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {γ : ℝ → M} {θ : ℝ → ℝ} {t : ℝ}
    (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ)
    (himm : Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) γ (θ t)))
    (hθd : MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal θ t)
    (hθ : HasStrictDerivAt θ (deriv θ t) t) (hθ' : deriv θ t ≠ 0) :
    Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (γ ∘ θ) t) := by
  have hne : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  have hchain := mfderiv_comp (I := Work.Noncompact.CompressionTube.MCreal)
    (I' := Work.Noncompact.CompressionTube.MCreal)
    (I'' := Work.Noncompact.CompressionTube.MC n) t (g := γ) (f := θ)
    (hγ.contMDiffAt.mdifferentiableAt hne) hθd
  rw [hchain]
  exact himm.comp (Work.Routing.injective_mfderiv_of_deriv_ne_zero hθ hθ')

/-- **The stage piece reparametrised to `[0,1]` with the initial germ kept verbatim.**

`P` is the glued piece of a stage, on `[0, L+1]`: its initial germ is the straight chart line
`c.symm (c σ + s • u)` on `[0, L+ε]` and its terminal germ is `c'.symm (c' q + (s-L-1) • wv)` on
`[L, L+1]`.  With `0 < δ`, `0 < δ'`, `δ + δ' < 1`, `δ ≤ ε`, there is `Q` on `[0,1]` with

* the **initial** germ `Q t = c.symm (c σ + t • u)` on `[0, δ]` — *same chart, same direction* `u`
  as the arriving piece's terminal germ (the junction row `Lane.hgerm`);
* the **terminal** germ `Q t = c'.symm (c' q + (t-1) • wv)` on `[1-δ', 1]` — same direction `wv`.

This is the row `StageState.hgin`/`hgout` of the next state; the naive rescaling
`t ↦ (L+1) * t` would give direction `(L+1) • u` and would therefore *not* satisfy `T.uout = S.uout`. -/
theorem exists_reparametrized_piece_sameGerm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hutgt : ∀ s : ℝ, 0 ≤ s → s ≤ L + ε → c σ + s • u ∈ c.target)
    {P : ℝ → M} (hPsm : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P)
    (hPimm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) (L + 1) → Function.Injective
      (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) P t))
    (hPinj : Set.InjOn P (Set.Icc (0:ℝ) (L + 1)))
    (hP0 : P 0 = σ)
    (hgermP : ∀ s : ℝ, 0 ≤ s → s ≤ L + ε → P s = c.symm (c σ + s • u))
    {q : M} {c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {wv : EuclideanSpace ℝ (Fin n)} (hwv : wv ≠ 0) (hPq : P (L + 1) = q)
    (hgermP' : ∀ t : ℝ, L ≤ t → t ≤ L + 1 → P t = c'.symm (c' q + (t - L - 1) • wv))
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (hδδ' : δ + δ' < 1) (hδε : δ ≤ ε) :
    ∃ Q : ℝ → M, ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder Q ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective
        (mfderiv Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n) Q t)) ∧
      Set.InjOn Q (Set.Icc (0:ℝ) 1) ∧
      Q 0 = σ ∧ Q 1 = q ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ δ → Q t = c.symm (c σ + t • u)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ δ → c σ + t • u ∈ c.target) ∧
      (∀ t : ℝ, 1 - δ' ≤ t → t ≤ 1 → Q t = c'.symm (c' q + (t - 1) • wv)) := by
  obtain ⟨χ, hχsmd, hid, hshift, hpos, hχ1, hχmem⟩ :=
    exists_stageReparam (L := L) hL hδ hδ' hδδ'
  have hχcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    contMDiff_iff_contDiff.mp hχsmd
  have hstrict : ∀ t : ℝ, HasStrictDerivAt χ (deriv χ t) t :=
    fun t => hχcd.hasStrictDerivAt (by simp)
  have hmd : ∀ t : ℝ, MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal χ t :=
    fun t => hχsmd.contMDiffAt.mdifferentiableAt (by simp)
  have hmono : StrictMono χ := strictMono_of_deriv_pos hpos
  have hδL : δ ≤ L + ε := by linarith
  refine ⟨fun t => P (χ t), hPsm.comp hχsmd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact injective_mfderiv_comp_reparam_at (n := n) (M := M) hPsm
      (hPimm (χ t) (hχmem t ht)) (hmd t) (hstrict t) (ne_of_gt (hpos t))
  · intro a ha b hb hab
    have hχa : χ a ∈ Set.Icc (0:ℝ) (L + 1) := hχmem a ha
    have hχb : χ b ∈ Set.Icc (0:ℝ) (L + 1) := hχmem b hb
    exact hmono.injective (hPinj hχa hχb hab)
  · show P (χ 0) = σ
    rw [hid 0 (by linarith), hP0]
  · show P (χ 1) = q
    rw [hχ1, hPq]
  · intro t ht0 htd
    show P (χ t) = c.symm (c σ + t • u)
    rw [hid t htd]
    exact hgermP t ht0 (le_trans htd hδL)
  · intro t ht0 htd
    exact hutgt t ht0 (le_trans htd hδL)
  · intro t ht1 _
    show P (χ t) = c'.symm (c' q + (t - 1) • wv)
    rw [hshift t ht1]
    have h1 : t + L - L - 1 = t - 1 := by ring
    rw [← h1] at *
    exact hgermP' (t + L) (by linarith) (by linarith)

end Work.Drive.TwoRays
