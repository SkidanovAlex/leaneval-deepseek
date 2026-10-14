import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS.LocData6.Small6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The far part `zfar L F_*` lies in `ℋ⁶`** for `L ≥ 1`, from the order-`6` jet bound of
`zfarR L` and the angular bound. -/
theorem HkMem_zfar_Fstar6 (α L : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    Work.Spaces.HkMem α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  obtain ⟨K, _hK, hmaj⟩ := HkIntegrand_zfar6_le α L hα hL hA hRθ hAz hΓ
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
    intro z hz θ hθ
    have h1 : Work.Spaces.HkIntegrand α 6
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
      refine le_trans (le_of_eq ?_) (hmaj z hz θ hθ)
      rw [show (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
          = fun z θ => (-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
              * Work.Spaces.Gam α θ from by
        funext z' θ'
        rw [Work.FTS.LocDataExt.zfar_Fstar_eq α L]
        ring]
    rwa [Work.FTS.LocData.HkIntegrand_neg α 6
      (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ] at h1
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.Stability.zfar L (Work.Construction.Fstar α))
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6 ?_ ?_ ?_ ?_
  · exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _
      (Work.FTS.LocData.SmoothQuad_zfar_Fstar α L)
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · exact hmaj'

/-- **THE ORDER-`6` SMALLNESS OF THE LOCALISED DATUM.**  For every `ε > 0` there is `L₀` such
that for every `L ≥ L₀` there is a scalar `β` with `|β| ≤ ε`, `L₁₂(locG α L β (hLoc α))(0) = 0`
and `Xn₆(locG α L β (hLoc α)) ≤ ε`. -/
theorem locG6_small (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ ε > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∃ β : ℝ,
      |β| ≤ ε ∧
        Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
        Xn6 α (locG6 α L β) ≤ ε := by
  intro ε hε
  obtain ⟨Kb, hKb0, hKb⟩ := hLoc_majorant6 α hα hα1
    (fun i hi θ hθ => hGam6 α hα hα1 hi hθ)
  obtain ⟨A, hA, hAz⟩ := zfarR_jet_le6_clean
  have hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 :=
    fun i hi θ hθ => hGam6 α hα hα1 hi hθ
  obtain ⟨Cz, _hCz0, hCz⟩ := HkSq_zfar_Fstar_le6 α hα hα1 (le_of_lt hA) (by norm_num)
    (fun L hL j hj z hz θ => hAz L hL j hj z hz θ) hΓ
  obtain ⟨L₀, hL₀⟩ := locData6_small_aux α hα hα1
    (Work.FTS.LocData.SmoothQuad_hLoc α)
    (fun z hz θ hθ => by
      rw [Real.sq_sqrt hKb0]
      exact hKb z hz θ hθ)
    (Work.FTS.LocData.L12_hLoc α hα hα1).2
    (fun L β hL => Work.FTS.LocData.L12_locG α L β hα hα1 hL)
    ⟨Cz, fun L hL => hCz L hL⟩
    (fun L hL => HkMem_zfar_Fstar6 α L hα hα1 hL (le_of_lt hA) (by norm_num)
      (fun j hj z hz θ => hAz L hL j hj z hz θ) hΓ)
    ε hε
  exact ⟨L₀, fun L hL => hL₀ L hL⟩

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The slot bound of the decay clause**: the majorant `Maj` dominates every mixed slot
`D_z^jD_θ^i f` of order `j + i ≤ k` on the open quadrant. -/
def SlotMaj (k : ℕ) (Maj : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z ∈ Set.Ioi 0, ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ k →
    |Work.Spaces.mixed j i f z θ| ≤ Maj z

/-- **The radial slot-decay clause of `EpsUniformMem`** (fifth interface repair; the lead's ruling
(G-B)).

The identification `hlim` of E5 (`epsRHSP … → rhsFun …`) has one step which is *not* a continuity
statement: the modulation constants `muDyn`/`lamDyn` are defined through the **zero modes**
`L₁₂(Y)(0) = ∫_0^∞ (1/s)∫_θ K(θ)Y(s,θ) dθ ds` (`Construction.mufunS`), and `L₁₂(·)(0)` is a bounded
functional on `ℋ⁴` (`OpenPkg.l12zero_field`) but *not* continuous along a locally uniformly
convergent sequence with uniform `ℋ⁴`/`ℋ⁶`-bounds: `Xn α (Y_n − Y) ↛ 0`.  The provable route — the
one the frozen `GalLimit` route also *assumes* under the names N1/N5 — is dominated convergence in
the radial variable, which needs a *majorant* `Maj` with `∫_0^∞ Maj(s)/s ds < ∞`, uniform in `ε`.

This definition names that clause.  `Maj` dominates the mixed slots of order `≤ 1` of the projected
slice `P₀ J_ε g(τ)`; the three elliptic blocks of `N α F Φ` (which is where the elliptic solution
`E (P₀ J_ε g(τ))` enters the right-hand side through `PhiTil`) are only **bounded, by the constant
`3`, on the open quadrant** (curric-46 repair 2026-10-12, `cbc/fts_e5swap_e4chapters.md` §B1 and
its REVIEW: the former clause "blocks `≤ Maj`" is refuted on the route — the explicit `Θ(F_*)` part
makes `|Uop/sin 2θ| ≥ 1` on all of `(0,1/10)`, so no `Maj` with `∫ Maj/z < ∞` dominates it
(`EpsE4Thr.C46B.not_EpsDecay`).  The blocks multiply slots of `F = F_* + W`, whose `F_*`-part is
`O(z/(1+z)²)` and whose `W`-part is `≤ Maj`, so a constant bound suffices for E5).  The clauses `0 ≤ Maj`,
`Maj ≤ 1` and the integrability of `Maj z / z` are part of it, so that *every* polynomial
combination of the slots which occurs in `N₀`, `N` and `Transport` is dominated by a fixed multiple
of `Maj` (+ the decaying `F_*`-slots) (the powers `Maj^k`, `k ≥ 1`, are dominated by `Maj` because `Maj ≤ 1`), and the three
zero-mode integrands are then dominated by multiples of `Maj(s)/s`.

The cap of the majorant is `Maj ≤ 1`.

Why these five profiles: the right-hand side of the scheme is
`dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ`, and `mufunS` reads off the three zero modes of
`N₀ α (Ftau α g τ) (slice g τ)`, `N α (Ftau α g τ) (slice (PsiCan Φs E g) τ)` and
`Transport (slice g τ)`.  In `N` only the *values* of `Rop`, `Uop/sin 2θ`, `Vop` of
`PhiTil α (Ftau) (slice (PsiCan …))` occur, together with the slots of `F = F_* + g` of order `≤ 1`;
in `N₀` only the slots of `F` of order `≤ 1` occur (the `F_*`-terms are fixed and decaying), and
`Transport f = 3 D_θ f/(1+z)` is of order `≤ 1` in `f`.  The fixed profile `F_* = α(Γ/c)·2z/(1+z)²`
decays like `z^{-1}` and its `L₁₂`-mode is `2α/(1+z)` (`Construction.L12_Fstar`) — no hypothesis is
needed for those. -/
def EpsDecay (α : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (ε τ : ℝ) (g : Fam)
    (Maj : ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ Maj z) ∧ (∀ z, Maj z ≤ 1) ∧
    MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
    SlotMaj 1 Maj (slice (JfamP ρ ε g) τ) ∧
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 ∧
      |Work.Construction.Uop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ
          / Work.Construction.s2 θ| ≤ 3 ∧
      |Work.Construction.Vop (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3

def EpsUniformMem (α : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ K : ℝ) : Prop :=
  (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧ Work.Construction.L12 g₀ 0 = 0 ∧
    ∀ T > 0, ∃ K' : ℝ, K ≤ K' ∧ ∃ ε₁ > 0, ∃ Maj : ℝ → ℝ,
      MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      ∀ ε ∈ Set.Ioc 0 ε₁, ∃ g : Fam,
      IsEpsSolP α ρ ε T Φs E g₀ g ∧
        ∀ τ ∈ Set.Icc 0 T,
          Work.FTS.EllipticEst.SmoothOpen (slice g τ) ∧
            Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ) ∧
            Work.Spaces.HkMem α 6 (slice g τ) ∧
            Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 ∧
            Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K' ∧
            Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ) ∧
            ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
            EpsDecay α ρ Φs E ε τ g Maj

/-- **`EpsUniformMem` is monotone in the two constants** (for `α ≥ 0`): the existential `K'` of the
definition absorbs the increase of `K`. -/
theorem EpsUniformMem.mono {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {C₀ K C₀' K' : ℝ} (h : EpsUniformMem α ρ Φs E g₀ C₀ K) (hα : 0 ≤ α) (h4 : C₀ ≤ C₀')
    (hK : K ≤ K') : EpsUniformMem α ρ Φs E g₀ C₀' K' := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro T hT
  obtain ⟨K'', hK'', ε₁, hε₁, Maj, hMajint, hg⟩ := h.2.2 T hT
  refine ⟨max K'' K', le_max_right _ _, ε₁, hε₁, Maj, hMajint, ?_⟩
  intro ε hε
  obtain ⟨g, hsol, hb⟩ := hg ε hε
  refine ⟨g, hsol, ?_⟩
  intro τ hτ
  exact ⟨(hb τ hτ).1, (hb τ hτ).2.1, (hb τ hτ).2.2.1,
    le_trans (hb τ hτ).2.2.2.1 (mul_le_mul_of_nonneg_right h4 (pow_nonneg hα 2)),
    le_trans (hb τ hτ).2.2.2.2.1 (le_max_left _ _), (hb τ hτ).2.2.2.2.2.1,
    (hb τ hτ).2.2.2.2.2.2.1, (hb τ hτ).2.2.2.2.2.2.2⟩

end Work.FTS.StrongEps
end
end
