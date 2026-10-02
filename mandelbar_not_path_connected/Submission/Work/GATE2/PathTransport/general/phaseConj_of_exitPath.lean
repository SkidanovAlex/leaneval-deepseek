import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.phase_of_chainWindow
import Submission.Work.GATE2.PathTransport.chainWindow_of_exitPath
import Submission.Work.GATE2.PathTransport.general.chainWindow_of_exitPath
import Submission.Work.GATE2.PathTransport.general.phase_of_chainWindow_local

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport.general

/-- **Both conjuncts of the phase residual from a single exit path, for a general root angle.**
This is `Work.GATE2.PathTransport.phaseConj_of_exitPath` with the root-angle hypothesis
`1023 α = 371` replaced by `∃ s : ℤ, 1023 α = s`, which covers **both** root angles of the design
(`1023 α₁ = 371` and `1023 α₂ = 404`, `Work.GATE2.alpha1_mul` / `Work.GATE2.alpha2_mul`).

`α₁` enters with the `b`-tongue and `α₂` with the `ι b`-tongue, so the two-tongue assembly
`Work.GATE2.phaseResidual_of_exitPath` needs exactly this general form.

The proof generalises the four ingredients of the `371` version — the arithmetic
`∃ t : ℤ, (1024^m − 1) α = t` (from `1023 ∣ 1024^m − 1` and `∃ s, 1023 α = s`), the angle equation
`A (F^[j] z) = 1024^j • A z`, the path transport of the deviation, the chain window
`Work.GATE2.PathTransport.chainWindow_of_exitPath` and the local phase identity
`Work.GATE2.phase_of_chainWindow_local` — all of which are on disk in the `371` form; each becomes
the general form by replacing `371` with the existentially given integer `s`. -/
theorem phaseConj_of_exitPath {e : ℂ} {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ)) {m : ℕ}
    (hm : 1 ≤ m) (σ : C(unitInterval, ℂ)) (h0 : σ 0 = e) (h1 : σ 1 = Work.EL.F e e)
    (hdev : ∀ t, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
      ((Work.EL.F e)^[m - 1] (σ t))| < (1 / 8192 : ℝ))
    (hpot : ∀ t, (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0 <
      Work.Bottcher.green e ((Work.EL.F e)^[m - 1] (σ t))) :
    |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)| <
        Work.Final.windowEps ∧
      Work.GATE.deviation (Work.Bottcher.varphiCrit e) α e =
        Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e) /
          (1024 : ℝ) ^ m := by
  -- the chain window supplied by PT, for the general root angle
  have hwin :=
    Work.GATE2.PathTransport.general.chainWindow_of_exitPath hα hm σ h0 h1 hdev hpot
  -- the whole chain `e, F_e e, …, F_e^[m-1] e` lies in the critical domain of `e`
  have hpot0 : (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0 <
      Work.Bottcher.green e ((Work.EL.F e)^[m - 1] e) := by
    have h := hpot 0
    rwa [h0] at h
  have hdom : ∀ i ≤ m - 1, (Work.EL.F e)^[i] e ∈ Work.ParamRays.critDomain e :=
    Work.GATE2.PathTransport.mem_critDomain_iterate (c := e) (z := e) (j := m - 1) hpot0
  refine ⟨?_, ?_⟩
  · -- first conjunct: PT at `k = m`, and `windowEps = 1/2048`
    have h := hwin m le_rfl
    simpa [Work.Final.windowEps, Work.Landing.windowEps] using h
  · -- second conjunct: the local phase identity along the chain window
    have hfun : ∀ k < m,
        Work.Bottcher.varphiCrit e (Work.EL.F e ((Work.EL.F e)^[k] e)) =
          (Work.Bottcher.varphiCrit e ((Work.EL.F e)^[k] e)) ^ (1024 : ℕ) := by
      intro k hk
      have hz := hdom k (Nat.le_sub_one_of_lt hk)
      simpa using (Work.GATE2.varphiCrit_F_iterate (c := e) hz 1).symm
    have hw : ∀ k < m,
        -(1 / 2048 : ℝ) < Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
            ((Work.EL.F e)^[k] e) ∧
          Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e) ≤
            (1 / 2048 : ℝ) := by
      intro k hk
      have h := hwin k (le_of_lt hk)
      exact ⟨(abs_lt.mp h).1, le_of_lt (abs_lt.mp h).2⟩
    have hkey := Work.GATE2.PathTransport.general.phase_of_chainWindow_local
      (c := e) (e := e) (φ := Work.Bottcher.varphiCrit e) m hα hfun hw
    rw [eq_div_iff (pow_ne_zero m (by norm_num : (1024 : ℝ) ≠ 0))]
    rw [hkey]
    ring

end Work.GATE2.PathTransport.general
