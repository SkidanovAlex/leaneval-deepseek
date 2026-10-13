/-
# `RegQo_dth_dz` — the `D_θ`/`D_z`-ports of the *open* coercivity class

`Work.FTS.StrongEps.EpsE4Thr.RegQo α k f` is `SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f`,
the open-quadrant (`C^∞` on `(0,∞) × (0,π/2)`, no `z`-flatness at `z = 0⁺`) version of the
frozen `Work.FTS.Nonlin.RegQ`.  This file proves the two index-raising ports of the class:

  `RegQo α (n+1) f → RegQo α n (D_θ f)`   and   `RegQo α (n+1) f → RegQo α n (D_z f)`.

They are the `SmoothOpen` counterparts of `Work.FTS.CoercivityFix.QuadPorts.RegQ_dth` /
`RegQ_dz` (which ask for the *analytic* class `SmoothQuad`); the only thing that changes on the
smaller domain is the smoothness component of the class and the commutation lemma `D_z`–`D_θ`
used by the `z`-index shift.  The two ports are logically independent and are assembled at the
end.

* **Smoothness** is preservation of `C^∞` on the open quadrant (`SmoothOpen.Dth`, `SmoothOpen.Dz`
  of `Submission/Work/FTS/EllipticEst/OpenQDefs.lean`).
* **`ℋⁿ`-membership.**  Every summand of `HkIntegrand α n (D_θ f)`, resp. of
  `HkIntegrand α n (D_z f)`, is a summand of `HkIntegrand α (n+1) f` with a comparable weight:
  * `D_θ` (see `Work.Coercivity.HkIntegrand_Dth_le`): the pure summands `D_z^i D_θ f` become the
    mixed summands `D_z^i D_θ^1 f` at level `n+1` (their weight `w sin^{-η/2}` is *lighter* than
    `W = w sin^{-γ/2}`), and the mixed summands are `D_z^j D_θ^{i+1} f` *definitionally*;
  * `D_z` (see `Work.FTS.EllipticEst.UopHk.HkIntegrand_Dz_le_succ`): the pure summands are
    `D_z^{i+1} f` definitionally, and the mixed summands are `D_z^{j+1} D_θ^i f` by Clairaut on
    the open quadrant (`mixed_Dz_shift`), the identity being global on `Iz × Iθ` because at
    `z = 0` and at the angular endpoints both sides vanish.
  The membership then follows from `Work.FTS.LocData.HkMem_of_majorant`, the majorant being the
  `(n+1)`-integrand of `f` itself and the measurability input the continuity of the integrand of
  the ported function on the open quadrant (`SmoothOpen.continuousOn_HkIntegrand`).
* **Boundary traces.**  `BdryTraces` only asks for one-sided limits through points of the
  domain: for `D_θ` the identity `D_z^b D_θ^a (D_θ f) = D_z^b D_θ^{a+1} f` is *global*, so a
  `simpa` reindexes; for `D_z` it holds on `Iz × Iθ` (`mixed_Dz_shift`), so the transport is
  through `Filter.Tendsto.congr'` along the eventual sets `Ioi 0`, `Ioo 0 (π/2)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkMem_dth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `D_θ`-port -/

/-- `D_θ` raises the angular order of the mixed derivatives by one:
`D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
private lemma mixed_Dth_shift_fts (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  simp only [Work.Spaces.mixed]
  have h : Work.Spaces.Dth f = Work.Spaces.DthIter 1 f := rfl
  rw [h, Work.Spaces.DthIter_add_right]

/-- **The boundary traces of `D_θ f`** from those of `f`, by the (global) reindexing of the
mixed derivatives: the traces of order `(a,b)` of `D_θ f` are the traces of order `(a+1,b)` of
`f`. -/
private lemma BdryTraces_Dth_fts {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hbd : Work.FTS.Nonlin.BdryTraces α (n + 1) f) :
    Work.FTS.Nonlin.BdryTraces α n (Work.Spaces.Dth f) := by
  intro a b hab
  have key : ∀ z θ, Work.Spaces.mixed b a (Work.Spaces.Dth f) z θ
      = Work.Spaces.mixed b (a + 1) f z θ := fun z θ => by rw [mixed_Dth_shift_fts]
  simpa only [key] using hbd (a + 1) b (by omega)

/-- **The `ℋⁿ`-membership of `D_θ f`**, by domination of its integrand by the `(n+1)`-integrand
of `f` (`Work.Coercivity.HkIntegrand_Dth_le`), through `HkMem_of_majorant`, the measurability
input being the continuity of the integrand of `D_θ f` on the open quadrant. -/
private lemma HkMem_Dth_fts {α : ℝ} (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    (hsm.Dth.continuousOn_HkIntegrand α n)
    hmem.1 hmem.2
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ)

/-! ## The `D_z`-port -/

/-- **The boundary traces of `D_z f`** from those of `f`: the traces at order `(a,b)` of `D_z f`
are the traces at order `(a,b+1)` of `f`, because the mixed derivatives agree on the domain
(`Work.FTS.EllipticEst.UopHk.mixed_Dz_shift`) and every one-sided limit is taken through points
of the domain. -/
private lemma BdryTraces_Dz_fts {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hbd : Work.FTS.Nonlin.BdryTraces α (n + 1) f) :
    Work.FTS.Nonlin.BdryTraces α n (Work.Spaces.Dz f) := by
  intro a b hab
  obtain ⟨hzlim, hθlim⟩ := hbd a (b + 1) (by omega)
  -- the two filters `𝓝[>] 0`, `𝓝[<] π/2` count the open interval as an eventual set
  have hmemGT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    (nhdsGT_basis_of_exists_gt ⟨π / 2, Real.pi_div_two_pos⟩).mem_of_mem Real.pi_div_two_pos
  have hmemLT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) :=
    (nhdsLT_basis_of_exists_lt ⟨0, by linarith [Real.pi_pos]⟩).mem_of_mem
      (by linarith [Real.pi_pos])
  constructor
  · intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    constructor
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a
            (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).1.congr' hev
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[atTop]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a
            (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).2.congr' hev
  · intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    constructor
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemGT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a hzIz
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).1.congr' hev
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[<] (π / 2)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemLT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [Work.FTS.EllipticEst.UopHk.mixed_Dz_shift hsm b a hzIz
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).2.congr' hev

/-- **The `ℋⁿ`-membership of `D_z f`**, by domination of its integrand by the `(n+1)`-integrand
of `f` (`Work.FTS.EllipticEst.UopHk.HkIntegrand_Dz_le_succ`, i.e. the index shift
`D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` on `Iz × Iθ`). -/
private lemma HkMem_Dz_fts {α : ℝ} {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkMem α n (Work.Spaces.Dz f) :=
  Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α n hsm hmem

/-! ## The two ports, assembled -/

theorem regQo_dth_dz {α : ℝ} {n : ℕ} {f : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dth f) ∧
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dz f) := by
  obtain ⟨hsm, hmem, hbd⟩ := hf
  exact ⟨⟨hsm.Dth, HkMem_Dth_fts hα hsm hmem, BdryTraces_Dth_fts hbd⟩,
    ⟨hsm.Dz, HkMem_Dz_fts hsm hmem, BdryTraces_Dz_fts hsm hbd⟩⟩

end Work.FTS.StrongEps.EpsE4Thr
