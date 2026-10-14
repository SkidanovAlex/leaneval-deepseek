import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotPairingSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLeafSqFKf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPsi6TermBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.Assembly
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.nsum_split6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.StrongPersist.H6Row6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinSqHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- **The level-six `ℋ⁶`-energy of the piece `sin²θ·(FK f)·f`**: for a datum
`DatData α f M` (so `√(HkSq α 4 f) ≤ M`) and `α ∈ (0,1]`,

  `HkSq α 6 (fun z θ => sin²θ · FK f z · f z θ) ≤ C · M² · HkSq α 6 f`.

Route (two of the three steps have proved templates in the tree):

1. **Pointwise σ²-multiplier comparison**: for every `m ≤ 6`, `SmoothOpen g` and `(z,θ)`,
   `HkIntegrand α m (fun z θ => sin²θ · g z θ) z θ ≤ Cloc m · HkIntegrand α m g z θ`.
   Proof: `fkSinSqLeibniz` expands the mixed slots as
   `mixed j i (σ²·g) = Σ_{r ≤ i} C(i,r) · DthIter r σ² · mixed j (i-r) g` on the open quadrant
   (`SmoothOpen σ²` is `fkSinSqLeibniz_sinSq_smoothOpen`), and `fkSinPow` gives
   `|DthIter r σ²| ≤ Ksin r · σ²` for `r ≥ 1` (while `DthIter 0 σ² = σ² ≤ 1`). The factor `σ²`
   is *absorbed by the weight*: with slot weights `Wt α = w·σ^{-γ/2}` and `w·σ^{-η/2}` one has
   `σ²·Wt α ≤ w·σ^{-η/2}` and `σ²·wσ^{-η/2} ≤ wσ^{-η/2}`, because `γ ≤ 2 + η`
   (`γ = 1 + α/10 ≤ 1.1`, `η = 99/100`), so each summand is dominated by a slot of
   `HkIntegrand α m g`. The `D_z`-slots are immediate since `σ²` is `θ`-only
   (`DzIter j (σ²·g) = σ²·DzIter j g`).
2. **θ-integrated matched majorant** (analogue of `FkAux.fkMulHkSqSliceLe` with `g := σ²·f`):
   for a.e. `z ∈ Iz`,
   `∫_θ HkIntegrand α 6 (fun z θ => FK f z · (sin²θ · f z θ)) z θ
      ≤ C · Σ_{b ≤ 6} (DzIter b (FK f) z 0)² · (∫_θ HkIntegrand α (6-b) f z θ)`.
   Proof: `radialMatchedMajorant` with `r := fun z => FK f z`, `g := fun z θ => sin²θ · f z θ`
   (Leibniz hypotheses `leibniz_rad_Dz_cd6`/`leibniz_rad_mixed_cd6`; `FK f` is `C⁶` by
   `contDiffOn6_FK`, `σ²·f` is `C⁶` on `Q0` since `f` is), integrated in `θ` as in
   `fkMulHkSqSliceLe`, using step 1 and `HkMem α (6-b) f` for the slice integrability.
3. **Assembly** (analogue of `FkAux.fkMulHkSqLe`): integrate step 2 in `z`; each term of the
   dominating sum is integrable and `≤ Cb · M² · HkSq α 6 f` by `FkAux.fkPsi6TermBound`.
`HkMem α 6 (fun z θ => sin²θ · FK f z · f z θ)` is conjunct 5 of `Npair6BWork.hkMem_fk_mul`. -/
theorem fkSinSqHkSq : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
        ≤ C * M ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Ca, hCapos, hA⟩ := fkSinSqMulSliceLe
  obtain ⟨Cb, hCbpos, hB⟩ := fkPsi6TermBound
  refine ⟨Ca * (7 * Cb) + 1, by positivity, ?_⟩
  intro α hα f M hD
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hα
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  set G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 7,
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) with hGdef
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hGdef]
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).1
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) z θ) ≤ Ca * G z := by
    filter_upwards [hA α hα f M hD] with z hz
    rw [hGdef]
    exact hz
  have hmono : Work.Spaces.HkSq α 6
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, Ca * G z := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) (hGint.const_mul Ca) hslice
  have hval : (∫ z in Work.Spaces.Iz, Ca * G z)
      = Ca * ∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    rw [hGdef, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
    · exact fun b hb =>
        (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).1
  have hterms : (∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)))
      ≤ ∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) := by
    refine Finset.sum_le_sum fun b hb => ?_
    exact (hB α hα f M hD b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).2
  have hsumval : (∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f))
      = 7 * (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, Ca * G z := hmono
    _ = Ca * ∑ b ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) := hval
    _ ≤ Ca * ∑ _b ∈ Finset.range 7, (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hterms (le_of_lt hCapos)
    _ = Ca * (7 * (Cb * M ^ 2 * Work.Spaces.HkSq α 6 f)) := by rw [hsumval]
    _ ≤ (Ca * (7 * Cb) + 1) * M ^ 2 * Work.Spaces.HkSq α 6 f := by
        nlinarith [hCapos, hCbpos, hSnn, hM2, sq_nonneg M, mul_nonneg hM2 hSnn]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux.glue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- `C⁶`-regularity on the open quadrant, the finite smoothness used by the pairing split. -/
abbrev Smooth6 (u : Fn) : Prop :=
  ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0

/-- **The pairing of a finite sum splits into the sum of the pairings** (for `N + 1` summands,
so that the base case is the single summand `u 0`).

By induction on `N`: the sum over `range (n+2)` is the sum over `range (n+1)` plus `u (n+1)`
(`Finset.sum_range_succ`), and the binary splitting is `N0pair6Aux.SlotPairingSplit6`, whose
hypotheses (`C⁶` + `ℋ⁶` honesty of the two summands and of the datum `f`) are supplied by the
induction hypothesis together with `H6Row6.NS6.hkMem_sum_range`. -/
theorem slotPairing_sum_range_succ {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f : Fn}
    (hf6 : Smooth6 f) (hfm : Work.Spaces.HkMem α 6 f) {u : ℕ → Fn} :
    ∀ N : ℕ, (∀ k ≤ N, Smooth6 (u k)) → (∀ k ≤ N, Work.Spaces.HkMem α 6 (u k)) →
      Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => ∑ k ∈ Finset.range (N + 1), u k z θ) f
        = ∑ k ∈ Finset.range (N + 1), Work.FTS.TransportS.slotPairing ρ a b (u k) f := by
  intro N
  induction N with
  | zero =>
      intro _ _
      have h0 : (fun z θ => ∑ k ∈ Finset.range (0 + 1), u k z θ) = u 0 := by
        funext z θ; rw [Finset.sum_range_one]
      rw [h0, Finset.sum_range_one]
  | succ n ih =>
      intro hcd hm
      have hcd' : ∀ k ≤ n, Smooth6 (u k) := fun k hk => hcd k (le_trans hk (Nat.le_succ n))
      have hm' : ∀ k ≤ n, Work.Spaces.HkMem α 6 (u k) :=
        fun k hk => hm k (le_trans hk (Nat.le_succ n))
      obtain ⟨hcdsum, hmsum⟩ :=
        Work.FTS.StrongPersist.H6Row6.NS6.hkMem_sum_range (n + 1) u
          (fun k hk => hcd k (le_of_lt hk))
          (fun k hk => hm k (le_of_lt hk))
      have hsplit : (fun z θ => ∑ k ∈ Finset.range (n + 1 + 1), u k z θ)
          = fun z θ => (∑ k ∈ Finset.range (n + 1), u k z θ) + u (n + 1) z θ := by
        funext z θ; rw [Finset.sum_range_succ]
      rw [hsplit,
        Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotPairingSplit6 (α := α) hα hab hρ
          (u₁ := fun z θ => ∑ k ∈ Finset.range (n + 1), u k z θ) (u₂ := u (n + 1)) (f := f)
          hcdsum (hcd (n + 1) le_rfl) hf6 hmsum (hm (n + 1) le_rfl) hfm,
        ih hcd' hm']
      conv_rhs => rw [Finset.sum_range_succ]

/-- **The assembly of the target bound from the twenty per-piece bounds.**

If every piece of the twenty-term sum satisfies `|slotPairing ρ a b (piece) f| ≤ C·S` with the
same constant and the nonnegative shape factor `S`, then the pairing of the sum — which is the
sum of the pairings, `slotPairing_sum_range_succ` — is at most `(20·C + 1)·S`. -/
theorem abs_slotPairing_sum_le {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f : Fn}
    (hf6 : Smooth6 f) (hfm : Work.Spaces.HkMem α 6 f) {u : ℕ → Fn}
    (hcd : ∀ k ≤ 19, Smooth6 (u k)) (hm : ∀ k ≤ 19, Work.Spaces.HkMem α 6 (u k))
    {C S : ℝ} (hC0 : 0 ≤ C) (hS0 : 0 ≤ S)
    (hpiece : ∀ k ≤ 19, |Work.FTS.TransportS.slotPairing ρ a b (u k) f| ≤ C * S) :
    |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => ∑ k ∈ Finset.range 20, u k z θ) f|
      ≤ (20 * C + 1) * S := by
  have hsplit : Work.FTS.TransportS.slotPairing ρ a b
      (fun z θ => ∑ k ∈ Finset.range 20, u k z θ) f
      = ∑ k ∈ Finset.range 20, Work.FTS.TransportS.slotPairing ρ a b (u k) f := by
    have h := slotPairing_sum_range_succ (α := α) hα hab hρ hf6 hfm 19 hcd hm
    simpa using h
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hcard : (Finset.range 20).card = 20 := Finset.card_range 20
  have hstep : (∑ k ∈ Finset.range 20,
        |Work.FTS.TransportS.slotPairing ρ a b (u k) f|) ≤ 20 * (C * S) := by
    have h := Finset.sum_le_card_nsmul (Finset.range 20)
      (fun k => |Work.FTS.TransportS.slotPairing ρ a b (u k) f|) (C * S)
      (fun k hk => hpiece k (by have := Finset.mem_range.mp hk; omega))
    rw [hcard] at h
    simpa using h
  have hCS : (0 : ℝ) ≤ C * S := mul_nonneg hC0 hS0
  have : (20 : ℝ) * (C * S) ≤ (20 * C + 1) * S := by nlinarith
  linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **The level-six product rule of Elgindi, in the `α`-free form on `(0,1]`.**

The tree's `N6.prod_field6` states the `ℋ⁶`-product rule with an existentially quantified
`α₂`; its proof (and the underlying `N6.prod_field_of6`) is valid for every `α ∈ (0,1]`, which
is the form below.  (`N6.prod_field_of6` is instantiated with the two analytic inputs
`N6.prod_majorant6` and `N6.exc_bound6`.) -/
theorem hkMem_mul_of6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u v : Fn}
    (hu : Work.FTS.VocabO.HQo α 6 u) (hv : Work.FTS.VocabO.HQo α 6 v) :
    Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) := by
  obtain ⟨K, hK, hMaj⟩ := Work.FTS.StrongPersist.N6.prod_majorant6
  obtain ⟨Ce, hCe, hExc⟩ := Work.FTS.StrongPersist.N6.exc_bound6
  obtain ⟨C, hC, hfield⟩ :=
    Work.FTS.StrongPersist.N6.prod_field_of6 ⟨K, hK, hMaj⟩ ⟨Ce, hCe, hExc⟩
  exact (hfield α hα hα1 u v hu hv).1

theorem nsumData (Ce : ℝ) : ∀ α ∈ Set.Ioc 0 1,
    ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs) ∧
      ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs))
        Work.FTS.EllipticEst.Q0 := by
  intro α hαIoc g Φ τ M Cs E Φs hτ hctx
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the slice and the perturbation stream function
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  set Ef : Fn := E f with hEf
  have hreg : Work.FTS.StrongPersist.H6Adm α f := hctx.hreg
  have hell : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f (Work.FTS.Galerkin.slice Φ τ) :=
    hctx.hell
  have hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs := hctx.hstar6
  -- the angular moment `FK f` is honest in `ℋ⁶` (the `α`-free membership)
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    fk_hkMem α hαIoc f hreg.reg.1 hreg.reg.2
  -- the `ℋ⁶ × ℋ⁶` product rule of the open-quadrant class, for this `α`
  have hmulSm : ∀ (u v : Fn), Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) :=
    fun u v hus hum hvs hvm => hkMem_mul_of6 hα0 hα1 ⟨hus, hum⟩ ⟨hvs, hvm⟩
  -- the bundled slice data
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs f Ef Φs :=
    { hα := hα0
      hα1 := hα1
      fsm := hreg.reg.1
      fm := hreg.reg.2
      f7 := hctx.h7
      Efsm := hell.hell.smooth
      Φssm := hell.hstar.smooth
      l12 := hreg.l12
      star := hstar6
      ell := hell.hell
      kfm := hkfm
      hadm := hreg
      mulSm := hmulSm }
  -- the twenty pieces, and their finite sum
  have hpcs := Work.FTS.StrongPersist.H6Row6.NS6.pieces D
  have hsum := Work.FTS.StrongPersist.H6Row6.NS6.hkMem_sum_range 20
    (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs)
    (fun k hk => (hpcs k hk).1) (fun k hk => (hpcs k hk).2)
  refine ⟨?_, ?_⟩
  · rw [Work.FTS.StrongPersist.H6Row6.pcs_sum]
    exact hsum.2
  · rw [Work.FTS.StrongPersist.H6Row6.pcs_sum]
    exact hsum.1

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
