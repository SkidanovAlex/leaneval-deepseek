import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Minimiser.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Minimiser.hSq_sub_le_of_dirForm_min`

Two unit vectors `r`, `s` of the Dirichlet energy space `Hsub N L` whose
excess energies `dirForm V p - m` (above the Rayleigh-quotient lower bound `m`)
are bounded by `Ar` resp. `As` have their difference controlled in the graph
norm by those excesses:

`hSq (r - s) ≤ Ar + As + 2 √(Ar As) + (m + K) * l2Sq (r - s)`  for `K ≥ 1`.

The mathematics is the Cauchy–Schwarz inequality for the *shifted* form

`B(p, q) = formP W (p) (q) - m * ⟪p.1, q.1⟫`

on `Hsub N L`, where `W` is the `L∞` class of the bounded potential `V`
(`formP` is the bilinear form of `Submission.Work.BoseSym.Minimiser.Defs`, whose
diagonal is `dirForm`).  The hypothesis `hray` says exactly that `B` is
positive semidefinite on `Hsub N L`, so `B(r, s) ≥ -√(B(r,r) B(s,s))`; since
`B(r,r) = dirForm V r - m ≤ Ar` and `B(s,s) ≤ As` (here `l2Sq r = l2Sq s = 1`),
the quadratic expansion

`B(r - s, r - s) = B(r,r) + B(s,s) - 2 B(r,s)`

yields `B(r-s, r-s) ≤ Ar + As + 2 √(Ar As)`.  Finally
`B(d,d) = gSq d + potSq V d - m * l2Sq d` with `potSq V d ≥ 0` because `V ≥ 0`
a.e. (`hVnn`), so `gSq d ≤ B(d,d) + m * l2Sq d` and, adding `l2Sq d = ‖d.1‖²`
to both sides and using `1 ≤ K`, the claim follows.

The bounds `C` of `V` and the a.e. measurability of `V` are used only to see
`V` as a class in `L^∞`, which is what makes `formP` available.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem hSq_sub_le_of_dirForm_min {N : ℕ} {L : ℝ} {V : Work.BoseSym.Conf N → ℝ} {C K m : ℝ}
    (hV : Work.BoseSym.BddBy N V C) (hVnn : Work.BoseSym.AENonneg N V) (hVm : Work.BoseSym.AEMeas N V)
    (hray : ∀ p : Work.BoseSym.Hsub N L,
      m * Work.BoseSym.l2Sq (p : Work.BoseSym.Amb N) ≤ Work.BoseSym.dirForm V (p : Work.BoseSym.Amb N))
    {r s : Work.BoseSym.Hsub N L} (hr : Work.BoseSym.l2Sq (r : Work.BoseSym.Amb N) = 1)
    (hs : Work.BoseSym.l2Sq (s : Work.BoseSym.Amb N) = 1)
    {Ar As : ℝ} (hAr : Work.BoseSym.dirForm V (r : Work.BoseSym.Amb N) - m ≤ Ar)
    (hAs : Work.BoseSym.dirForm V (s : Work.BoseSym.Amb N) - m ≤ As)
    (hAr0 : 0 ≤ Ar) (hAs0 : 0 ≤ As) (hK : 1 ≤ K) :
    Work.BoseSym.hSq ((r : Work.BoseSym.Amb N) - (s : Work.BoseSym.Amb N)) ≤
      Ar + As + 2 * Real.sqrt (Ar * As) +
        (m + K) * Work.BoseSym.l2Sq ((r : Work.BoseSym.Amb N) - (s : Work.BoseSym.Amb N)) := by
  -- The two hypotheses `0 ≤ Ar`, `0 ≤ As` are not needed below (the proof uses
  -- only `0 ≤ Brr ≤ Ar` and `0 ≤ Bss ≤ As`, which follow from `hray`), but they
  -- are part of the interface; the induced nonnegativity of the product is
  -- recorded here.
  have hArAs0 : 0 ≤ Ar * As := mul_nonneg hAr0 hAs0
  -- the potential `V` as a class in `L^∞`, so that `formP` applies to it
  have hVmem : MemLp V (⊤ : ℝ≥0∞) (volC N) :=
    memLp_top_of_bound hVm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hV x)
  let Wop : L2top N := hVmem.toLp V
  have hWop_ae : (Wop : Conf N → ℝ) =ᵐ[volC N] V := MemLp.coeFn_toLp hVmem
  -- the diagonal of `formP Wop` is the Dirichlet form of `V`
  have hdiag : ∀ p : Amb N, formP Wop p p = dirForm V p := fun p => by
    rw [formP_self, dirForm, inner_lpSMul_eq_potSq hWop_ae p]
  -- the shifted form is positive semidefinite on the energy space
  have hpos : ∀ p : Hsub N L,
      0 ≤ formP Wop (p : Amb N) (p : Amb N) - m * inner ℝ (p : Amb N).1 (p : Amb N).1 := by
    intro p
    have h := hray p
    rw [← hdiag (p : Amb N), l2Sq_eq_inner] at h
    linarith
  -- Cauchy–Schwarz for the shifted form
  have hcs := shiftH_sq_le Wop m hpos r s
  set Brr : ℝ := formP Wop (r : Amb N) (r : Amb N) - m * inner ℝ (r : Amb N).1 (r : Amb N).1
    with hBrr
  set Bss : ℝ := formP Wop (s : Amb N) (s : Amb N) - m * inner ℝ (s : Amb N).1 (s : Amb N).1
    with hBss
  set Brs : ℝ := formP Wop (r : Amb N) (s : Amb N) - m * inner ℝ (r : Amb N).1 (s : Amb N).1
    with hBrs
  have hBrr0 : 0 ≤ Brr := by rw [hBrr]; exact hpos r
  have hBss0 : 0 ≤ Bss := by rw [hBss]; exact hpos s
  have hBrrA : Brr ≤ Ar := by
    have h : Brr = dirForm V (r : Amb N) - m := by
      rw [hBrr, hdiag (r : Amb N), ← l2Sq_eq_inner (r : Amb N), hr, mul_one]
    rw [h]
    exact hAr
  have hBssA : Bss ≤ As := by
    have h : Bss = dirForm V (s : Amb N) - m := by
      rw [hBss, hdiag (s : Amb N), ← l2Sq_eq_inner (s : Amb N), hs, mul_one]
    rw [h]
    exact hAs
  -- the crossed term is bounded below
  have hBrs_ge : -Real.sqrt (Ar * As) ≤ Brs := by
    have h1 : |Brs| ≤ Real.sqrt (Brr * Bss) := by
      have h := Real.sqrt_le_sqrt hcs
      rwa [Real.sqrt_sq_eq_abs] at h
    have h2 : Real.sqrt (Brr * Bss) ≤ Real.sqrt (Ar * As) :=
      Real.sqrt_le_sqrt (mul_le_mul hBrrA hBssA hBss0 (le_trans hBrr0 hBrrA))
    have h3 := (abs_le.mp h1).1
    linarith
  -- the quadratic expansion of the shifted form on the difference
  have hexp : formP Wop ((r : Amb N) - (s : Amb N)) ((r : Amb N) - (s : Amb N))
      - m * inner ℝ (((r : Amb N) - (s : Amb N)).1) (((r : Amb N) - (s : Amb N)).1)
      = Brr + Bss - 2 * Brs := by
    rw [hBrr, hBss, hBrs, formP_sub_self]
    rw [Prod.fst_sub, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm (s : Amb N).1 (r : Amb N).1]
    ring
  have hBd_le : formP Wop ((r : Amb N) - (s : Amb N)) ((r : Amb N) - (s : Amb N))
      - m * inner ℝ (((r : Amb N) - (s : Amb N)).1) (((r : Amb N) - (s : Amb N)).1)
      ≤ Ar + As + 2 * Real.sqrt (Ar * As) := by
    rw [hexp]
    linarith
  -- the potential part of the difference is nonnegative (`V ≥ 0` a.e.)
  have hpotnn : 0 ≤ potSq V ((r : Amb N) - (s : Amb N)) := by
    rw [potSq]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hVnn] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  -- hence the gradient part of the difference is controlled by `hBd_le`
  have hgSq_le : gSq ((r : Amb N) - (s : Amb N))
      ≤ Ar + As + 2 * Real.sqrt (Ar * As) + m * l2Sq ((r : Amb N) - (s : Amb N)) := by
    have hBd_eq : formP Wop ((r : Amb N) - (s : Amb N)) ((r : Amb N) - (s : Amb N))
        - m * inner ℝ (((r : Amb N) - (s : Amb N)).1) (((r : Amb N) - (s : Amb N)).1)
        = gSq ((r : Amb N) - (s : Amb N)) + potSq V ((r : Amb N) - (s : Amb N))
          - m * l2Sq ((r : Amb N) - (s : Amb N)) := by
      rw [formP_self, inner_lpSMul_eq_potSq hWop_ae, ← l2Sq_eq_inner]
    rw [hBd_eq] at hBd_le
    linarith
  -- add the `L²` part of the graph norm, and use `1 ≤ K`
  have hl2nn : 0 ≤ l2Sq ((r : Amb N) - (s : Amb N)) := by
    rw [l2Sq]; positivity
  rw [hSq]
  nlinarith [hgSq_le, hl2nn, hK]

end

end Work.BoseSym.Minimiser
