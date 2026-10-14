import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.STEasyId
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.VocabO
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false

/-- **`L₁₂(F)` is `C^k` on `(0,∞)`** for `F` smooth on the open quadrant with `HkMem α k F`,
`k ≥ 2`, `0 < α`.  (`GsingFactsInterior` supplies the `C^{k-1}` statement together with the
derivative `-3F_*(F)(z)/z`, which is `C^{k-1}`; one order is gained.) -/
theorem contDiffOn_L12_k (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (hk : 2 ≤ k) :
    ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi 0) := by
  obtain ⟨_, hderiv⟩ := contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem (by omega)
  have hg : ContDiffOn ℝ (k - 1) (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) :=
    ((contDiffOn_const.mul hFstar).div contDiffOn_id fun z hz => ne_of_gt hz).neg
  have h := contDiffOn_succ_of_hasDerivAt
    (f := Work.Elliptic.L12 F) (g := fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
    (m := k - 1)
    (fun z hz => by
      have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
      have h1 := hderiv z hz'
      refine h1.congr_deriv ?_
      ring)
    hg
  have hcast : ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k : ℕ) : ℕ∞ω) := by
    calc ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k - 1 + 1 : ℕ) : ℕ∞ω) := by
          rw [Nat.cast_add, Nat.cast_one]
      _ = ((k : ℕ) : ℕ∞ω) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  simpa only [hcast] using h


end Work.FTS.EllipticEst.UopHk
end
end
-- ===== merged: Submission.Work.FTS.H2.AesmSlicesQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.LocData (Qd SmoothQuad)

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Continuity of the mixed derivatives of a `SmoothQuad` function -/





/-- `D_z` of a `SmoothQuad` function is `SmoothQuad`. -/
private lemma smoothQuad_Dz {G : ℝ → ℝ → ℝ} (hG : SmoothQuad G) :
    SmoothQuad (Work.Spaces.Dz G) :=
  Work.FTS.LocData.contDiffOn_Dz Work.FTS.LocData.isOpen_quadU hG

/-! ## Joint continuity of `H4PairInt` on the open square -/


/-! ## Joint continuity of `Hhard` on the open square -/




/-! ## The a.e. strong measurability statements -/


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.TransportS.Defs =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The slot weight of the flat `ℋ⁴`-pairing -/

/-- The angular weight of the slot `(a,b)` of the flat `ℋ⁴`-pairing: `(Whz)²` for the
`D_z`-only slots (`a = 0`) and `(Wm)²` for the slots with a `θ`-derivative (`a ≥ 1`).

On the open quadrant (`sin (2θ) > 0`) this is `w(z)² sin(2θ)^{-η}` resp.
`w(z)² sin(2θ)^{-γ}` (`hbi_Whz_sq`, `hbi_Wm_sq` of `Submission/Work/FTS/H2/HeasyBlocksId.lean`). -/
def slotW (α : ℝ) (a : ℕ) : ℝ → ℝ → ℝ :=
  if a = 0 then fun z θ => (Work.FTS.H2.Whz z θ) ^ 2
  else fun z θ => (Work.FTS.H2.Wm α z θ) ^ 2

@[simp] theorem slotW_zero (α : ℝ) :
    slotW α 0 = fun z θ => (Work.FTS.H2.Whz z θ) ^ 2 := rfl

theorem slotW_of_ne (α : ℝ) {a : ℕ} (ha : a ≠ 0) :
    slotW α a = fun z θ => (Work.FTS.H2.Wm α z θ) ^ 2 := by
  simp only [slotW, if_neg ha]

theorem slotW_of_pos' (α : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    slotW α a = fun z θ => (Work.FTS.H2.Wm α z θ) ^ 2 :=
  slotW_of_ne α (by omega)

/-- The slot weight is nonnegative (it is a square, uniformly in `α` and `a`). -/
theorem slotW_nonneg (α : ℝ) (a : ℕ) (z θ : ℝ) : 0 ≤ slotW α a z θ := by
  unfold slotW
  split_ifs <;> exact sq_nonneg _

/-- On the open quadrant the slot weight of a `D_z`-only slot is `w² sin(2θ)^{-η}`. -/
theorem slotW_zero_eq (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    slotW α 0 z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  simp only [slotW, if_pos rfl]
  exact Work.FTS.H2.hbi_Whz_sq z θ hs

/-- On the open quadrant the slot weight of a slot with a `θ`-derivative is
`w² sin(2θ)^{-γ}`. -/
theorem slotW_of_pos_eq (α : ℝ) {a : ℕ} (ha : 1 ≤ a) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    slotW α a z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [slotW_of_pos' α ha]
  exact Work.FTS.H2.hbi_Wm_sq α z θ hs


/-! ## The slot decomposition of the flat `ℋ⁴`-pairing

`H4PairInt α u v z θ` is the sum, over the slots `(a,b)`, of
`slotW α a z θ * mixed b a u z θ * mixed b a v z θ` (with the `D_z`-only slots indexed by
`b = a`).  The lemma below records this identification, the algebraic input of every
`IP4`-slot reduction. -/




/-! ## The API of the flat angular coefficient norm `CoefTh`

`CoefTh l f = ∑_{b < l+1} ∑_{i < l+1} [b + i ≤ l] supAbsO (D_z^b D_θ^i ∂_θ f)`, where
`supAbsO` is the supremum over the **open** quadrant `(0,∞) × (0,π/2)`.  Since `supAbsO` of
an unbounded function is Lean's junk value `0`, the companion honesty predicate
`CoefThMem l f` (every one of the finitely many functions is bounded on the open quadrant)
is needed for every *lower* bound on `CoefTh`; the lemmas below make that explicit. -/

/-- `supAbsO` is nonnegative. -/
theorem supAbsO_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.H2.supAbsO g := by
  have hπ : (1 : ℝ) < π / 2 := by have := Real.pi_gt_three; linarith
  have hmem : |g 1 1| ∈ {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧
      y = |g z θ|} := ⟨1, one_pos, 1, one_pos, hπ, rfl⟩
  by_cases hb : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧
      y = |g z θ|}
  · exact le_trans (abs_nonneg _) (le_csSup hb hmem)
  · rw [Work.FTS.H2.supAbsO, Real.sSup_def, dif_neg (fun h => hb h.2)]


/-- `CoefTh l f` is a sum of nonnegative terms, hence nonnegative. -/
theorem coefTh_nonneg (l : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.VocabO.CoefTh l f := by
  unfold Work.FTS.VocabO.CoefTh
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact supAbsO_nonneg _
  · exact le_refl 0

/-- Explicit sup bounds on the constituents of `CoefTh` give a bound on `CoefTh`. -/
theorem coefTh_le_of_supAbsO_le {l : ℕ} {f : ℝ → ℝ → ℝ} {K : ℝ}
    (h : ∀ b i : ℕ, b + i ≤ l →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) ≤ K) :
    Work.FTS.VocabO.CoefTh l f ≤ (((l : ℝ) + 1) * ((l : ℝ) + 1)) * K := by
  have hK : 0 ≤ K := le_trans (supAbsO_nonneg _) (h 0 0 (by omega))
  have hterm : ∀ b i : ℕ,
      (if b + i ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) ≤ K := by
    intro b i
    by_cases hbi : b + i ≤ l
    · rw [if_pos hbi]; exact h b i hbi
    · rw [if_neg hbi]; exact hK
  have hcard : ((Finset.range (l + 1)).card : ℝ) = (l : ℝ) + 1 := by simp
  have hinner : ∀ b : ℕ,
      (∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
        ≤ ((l : ℝ) + 1) * K := by
    intro b
    have h1 : (∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
        ≤ ∑ _i ∈ Finset.range (l + 1), K :=
      Finset.sum_le_sum fun i _ => hterm b i
    rwa [Finset.sum_const, nsmul_eq_mul, hcard] at h1
  have h2 : (∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
      ≤ ∑ _b ∈ Finset.range (l + 1), ((l : ℝ) + 1) * K :=
    Finset.sum_le_sum fun b _ => hinner b
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at h2
  unfold Work.FTS.VocabO.CoefTh
  refine le_trans h2 ?_
  exact le_of_eq (mul_assoc ((l : ℝ) + 1) ((l : ℝ) + 1) K).symm

/-- **Every single `supAbsO` occurring in `CoefTh` is dominated by `CoefTh`.**  (No honesty
hypothesis is needed: the other terms are nonnegative.) -/
theorem supAbsO_le_coefTh {l : ℕ} {f : ℝ → ℝ → ℝ} {b i : ℕ} (hbi : b + i ≤ l) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
      ≤ Work.FTS.VocabO.CoefTh l f := by
  have hmem : b ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have hmem' : i ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have houter : ∀ b' ∈ Finset.range (l + 1),
      0 ≤ ∑ i' ∈ Finset.range (l + 1),
        (if b' + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth f)) else 0) := by
    intro b' _
    refine Finset.sum_nonneg fun i' _ => ?_
    by_cases h : b' + i' ≤ l
    · rw [if_pos h]; exact supAbsO_nonneg _
    · simp [if_neg h]
  have hsingle : (∑ i' ∈ Finset.range (l + 1),
        (if b + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0))
      ≤ ∑ b' ∈ Finset.range (l + 1), ∑ i' ∈ Finset.range (l + 1),
        (if b' + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth f)) else 0) :=
    Finset.single_le_sum (f := fun (b' : ℕ) => ∑ i' ∈ Finset.range (l + 1),
        (if b' + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth f)) else 0))
      houter hmem
  have hinner : Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
      ≤ ∑ i' ∈ Finset.range (l + 1),
        (if b + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0) := by
    have h0 : ∀ i' ∈ Finset.range (l + 1),
        0 ≤ (if b + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0) := by
      intro i' _
      by_cases hbi' : b + i' ≤ l
      · rw [if_pos hbi']; exact supAbsO_nonneg _
      · simp [if_neg hbi']
    have h1 := Finset.single_le_sum (f := fun (i' : ℕ) => (if b + i' ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0)) h0 hmem'
    rwa [if_pos hbi] at h1
  unfold Work.FTS.VocabO.CoefTh
  exact le_trans hinner hsingle



end Work.FTS.TransportS
end
end
