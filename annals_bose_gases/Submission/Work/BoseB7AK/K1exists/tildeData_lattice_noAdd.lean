import Mathlib.Tactic.Have
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseB4.TildeDataInst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K1exists.tildeData_lattice_noAdd`

Node `B7A`'s `TildeData` on the box mode system (K1) for FS's concrete cubic box
and dual-lattice momenta, **without** the additivity hypothesis
`had : kmom (i - j) = kmom i - kmom j` of
`Work.BoseB4.exists_tildeData_lattice`.

That hypothesis was used in the corpus only through its consequence `kmom 0 = 0`,
which follows from the oddness `kmom (-i) = -kmom i` alone (`kmom 0 = kmom (-0)
= -kmom 0` in a real vector space, so `2 • kmom 0 = 0`).  Dropping `had` is
therefore a matter of re-running the same construction without it:

* `kmom_zero` — `kmom 0 = 0` from oddness;
* `exists_gram_jointKernel_noAdd` — the joint Gram model
  `Work.BoseB4.exists_gram_jointKernel` (the χ-modes and the θ-modes in one
  coordinate system) with `had` dropped from the hypotheses (it was used there
  only to derive `kmom 0 = 0`, in a line whose result is unused);
* `tildeData_lattice_noAdd` — the target, whose proof is the proof of
  `Work.BoseB4.exists_tildeData_lattice` with the single use of `had` replaced by
  `kmom_zero`.

The θ-mode orthogonality hypotheses are discharged from the lattice data exactly
as in `exists_tildeData_lattice`
(`Work.BoseB4.realIP_thetaExp_thetaExp_of_cell`,
`Work.BoseB4.realIP_thetaExp_thetaFun_of_cell`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB7AK.K1exists

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `kmom 0 = 0` from the oddness of `kmom` alone: `kmom 0 = kmom (-0) = -kmom 0`,
hence `2 • kmom 0 = 0`. -/
lemma kmom_zero {Mode : Type*} [AddCommGroup Mode] (kmom : Mode → ℝ³)
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) : kmom 0 = 0 := by
  have h : kmom (0 : Mode) = -kmom 0 := by simpa using hkmom 0
  have h2 : (2 : ℝ) • kmom 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **The joint Gram model without `had`.**  The statement of
`Work.BoseB4.exists_gram_jointKernel` with the additivity hypothesis removed:
there are coordinates in which the χ-modes have the box kernel as their Gram
matrix, the θ-modes are orthonormal on the non-zero modes, and the cross Gram
products are the overlaps `⟨e^{isx}θ, qVec ℓ k⟩` (normalised).

The proof is the proof of `Work.BoseB4.exists_gram_jointKernel`: the joint family
`V = {qVec ℓ ∘ kmom} ∪ {thetaExp ℓ ∘ kmom}` on `Mode ⊕ Mode` is a family of honest
`L²(Λ)` vectors, so its Gram kernel is symmetric and positive semidefinite, and
`Work.BoseB4.Exists_gram_iff` turns it into coordinates; rescaling by
`(ℓ³)^{-1/2}` normalises the two blocks.  The additivity hypothesis entered that
proof only in a line deriving `kmom 0 = 0` (whose result is never used), so it can
simply be deleted. -/
theorem exists_gram_jointKernel_noAdd (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → ℝ³)
    (horth : ∀ s t : Mode, s ≠ 0 → t ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaExp ℓ (kmom t)) = if s = t then ℓ ^ 3 else 0)
    (horthC : ∀ s : Mode, s ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaFun ℓ) = 0) :
    ∃ m : ℕ, ∃ f g : Mode → Fin m → ℝ,
      (∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
        = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
      ∧ (∀ s t : Mode, s ≠ 0 → t ≠ 0 →
          Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
      ∧ (∀ s k : Mode, s ≠ 0 →
          Work.BoseB4.gram (g s) (f k) = B.hatChi (ℓ • (kmom k - kmom s))) := by
  classical
  -- the joint two-block family: χ-modes on `inl`, θ-modes on `inr`
  let V : Mode ⊕ Mode → ℝ³ → ℂ :=
    Sum.elim (fun k => B.qVec ℓ (kmom k)) (fun s => B.thetaExp ℓ (kmom s))
  have hSym : ∀ p q : Mode ⊕ Mode, B.realIP (V p) (V q) = B.realIP (V q) (V p) :=
    fun p q => Work.BoseB4.realIP_comm B _ _
  have hInt : ∀ p q : Mode ⊕ Mode,
      Integrable fun x => ((starRingEnd ℂ) (V p x) * V q x).re := by
    rintro (i | i) (j | j)
    · exact B.integrable_conj_qVec_qVec hℓ (kmom i) (kmom j)
    · exact B.integrable_conj_qVec_thetaExp hℓ (kmom i) (kmom j)
    · exact B.integrable_conj_thetaExp_qVec hℓ (kmom i) (kmom j)
    · exact B.integrable_conj_thetaExp_thetaExp (kmom i) (kmom j)
  -- the joint kernel is positive semidefinite: it is the Gram kernel of `V`
  have hPSD : ∀ v : Mode ⊕ Mode → ℝ,
      0 ≤ ∑ i, ∑ j, v i * B.realIP (V i) (V j) * v j := by
    intro v
    have h := Work.BoseB4.realIP_sum_sum_nonneg B V v hInt
    have heq : (∑ p, ∑ q, v p * v q * B.realIP (V p) (V q))
        = ∑ p, ∑ q, v p * B.realIP (V p) (V q) * v q := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [heq] at h
    exact h
  obtain ⟨m, u, hu⟩ :=
    (Work.BoseB4.Exists_gram_iff (fun p q : Mode ⊕ Mode => B.realIP (V p) (V q))).mpr
      ⟨hSym, hPSD⟩
  -- the normalisation `c = (ℓ³)^{-1/2}`, so that `c²·ℓ³ = 1`
  set c : ℝ := Real.sqrt ((ℓ ^ 3)⁻¹) with hcdef
  have hc3 : c * c * ℓ ^ 3 = 1 := by
    have hsq : c * c = (ℓ ^ 3)⁻¹ := by
      rw [show c * c = c ^ 2 by ring, hcdef, Real.sq_sqrt (by positivity)]
    rw [hsq, inv_mul_cancel₀ (by positivity : ℓ ^ 3 ≠ 0)]
  have hcancel : ∀ Y : ℝ, c * c * (ℓ ^ 3 * Y) = Y := by
    intro Y
    rw [show c * c * (ℓ ^ 3 * Y) = (c * c * ℓ ^ 3) * Y by ring, hc3, one_mul]
  refine ⟨m, fun k => c • u (Sum.inl k), fun s => c • u (Sum.inr s), ?_, ?_, ?_⟩
  · -- the χ-block: FS `eq:Commutator_general`
    intro i j
    have h1 : B.realIP (V (Sum.inl i)) (V (Sum.inl j))
        = ℓ ^ 3 * B.boxKernel ℓ (kmom i) (kmom j) := by
      simpa only [V, Sum.elim_inl] using Work.BoseB4.realIP_qVec_qVec B hℓ (kmom i) (kmom j)
    rw [Work.BoseB4.gram_smul_smul, hu (Sum.inl i) (Sum.inl j), h1]
    simp only [Work.BoseB4.BoxData.boxKernel, Work.BoseB7.ccrKernel]
    exact hcancel _
  · -- the θ-block: orthonormal for the non-zero lattice momenta
    intro s t hs ht
    have h1 : B.realIP (V (Sum.inr s)) (V (Sum.inr t)) = if s = t then ℓ ^ 3 else 0 := by
      simpa only [V, Sum.elim_inr] using horth s t hs ht
    rw [Work.BoseB4.gram_smul_smul, hu (Sum.inr s) (Sum.inr t), h1]
    by_cases h : s = t
    · rw [if_pos h, if_pos h]
      exact hc3
    · rw [if_neg h, if_neg h, mul_zero]
  · -- the cross block: the FS cross kernel `χ̂(ℓ(k−s))`
    intro s k hs
    have h1 : B.realIP (V (Sum.inr s)) (V (Sum.inl k))
        = ℓ ^ 3 * B.hatChi (ℓ • (kmom k - kmom s)) := by
      simpa only [V, Sum.elim_inr, Sum.elim_inl] using
        Work.BoseB4.BoxData.realIP_thetaExp_qVec B hℓ (kmom s) (kmom k) (horthC s hs)
    rw [Work.BoseB4.gram_smul_smul, hu (Sum.inr s) (Sum.inl k), h1]
    exact hcancel _

/-- **K1 for FS's concrete box, without the additivity hypothesis.**  For a
`BoxData` on the unit cube, the side `ℓ > 0`, and an *injective* momentum
assignment whose values are dual-lattice momentum vectors `ℓ⁻¹ • 2π n`, node
`B7A`'s `TildeData` exists on the box mode system.  The θ-mode orthogonality
hypotheses of `Work.BoseB4.exists_tildeData` are discharged by
`Work.BoseB4.realIP_thetaExp_thetaExp_of_cell` / `..._thetaFun_of_cell`, and the
additivity hypothesis `had` of `Work.BoseB4.exists_tildeData_lattice` is not
needed (only `kmom 0 = 0`, which follows from oddness). -/
theorem tildeData_lattice_noAdd (B : Work.BoseB4.BoxData) (hcell : B.cell = Work.BoseB4.unitCell)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (kmom : Mode → EuclideanSpace ℝ (Fin 3)) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (hinj : Function.Injective kmom)
    (hlat : ∀ s : Mode, ∃ n : Fin 3 → ℤ, kmom s = ℓ⁻¹ • Work.BoseB4.vec n) :
    ∃ (m : ℕ) (f g : Mode → Fin m → ℝ)
      (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j) =
        Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)),
      Nonempty (Work.BoseB7A.TildeData (Work.BoseB4.boxFockData B kmom hkmom m f hf)) := by
  have hcancel : ∀ {v w : ℝ³}, (ℓ⁻¹ : ℝ) • v = ℓ⁻¹ • w → v = w := by
    intro v w h
    have := congrArg (fun u : ℝ³ => ℓ • u) h
    simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ)] using this
  have hvec0 : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [Work.BoseB4.vec]
  have h0 : kmom (0 : Mode) = 0 := kmom_zero kmom hkmom
  -- θ/θ orthogonality at dual-lattice momenta
  have horth : ∀ s t : Mode, s ≠ 0 → t ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaExp ℓ (kmom t)) = if s = t then ℓ ^ 3 else 0 := by
    intro s t hs ht
    obtain ⟨n, hn⟩ := hlat s
    obtain ⟨p, hp⟩ := hlat t
    have hiff : n = p ↔ s = t := by
      constructor
      · intro hnp
        exact hinj (by rw [hn, hp, hnp])
      · intro hst
        refine Work.BoseB4.vec_injective (hcancel ?_)
        rw [← hn, ← hp, hst]
    rw [hn, hp, Work.BoseB4.realIP_thetaExp_thetaExp_of_cell B hcell hℓ n p]
    exact if_congr hiff rfl rfl
  -- θ/condensate orthogonality at dual-lattice momenta
  have horthC : ∀ s : Mode, s ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaFun ℓ) = 0 := by
    intro s hs
    obtain ⟨n, hn⟩ := hlat s
    rw [hn, Work.BoseB4.realIP_thetaExp_thetaFun_of_cell B hcell hℓ n, if_neg ?_]
    intro hn0
    exact hs (hinj (by rw [hn, hn0, hvec0, smul_zero, h0]))
  obtain ⟨m, f, g, hf, hg, _⟩ := exists_gram_jointKernel_noAdd B hℓ kmom horth horthC
  exact ⟨m, f, g, hf, ⟨Work.BoseB4.tildeData B kmom hkmom m f g hf hg⟩⟩

end Work.BoseB7AK.K1exists
