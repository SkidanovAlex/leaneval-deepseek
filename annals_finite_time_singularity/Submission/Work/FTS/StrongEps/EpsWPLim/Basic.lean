/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsWPLim/Basic.lean`

Tools for the pointwise limit of the scheme's pre-mollified right-hand side
`epsWP α ρ ε Φs E g s` (the `E5` identification step): the extraction of the pointwise slot
convergence at a point `p` of the open quadrant from the local uniform convergence hypothesis
`hconv` of `epsWP_tendsto`, the `F_*`-additivity of the mixed slots and of the angular moment
`FK`, and the pointwise limit of `Construction.N` from the slot convergence of `PhiTil`.

* `tendsto_mixed_at` — local uniform convergence on the compacts of `Q0` gives, at any
  `p ∈ Q0`, the pointwise convergence of every `mixed j i`, `j + i ≤ 1` (the compact tube
  around `p` is the one used by `L12/linPart_tendsto`).
* `mixed_Fstar_add` / `FK_Fstar_add_of_SmoothOpen_HkMem` — the identification lemmas for the
  raw slice `w` and the profile `Ftau α g s = F_* + w`: `mixed j i (F_* + w) = mixed j i F_* +
  mixed j i w` (from `SmoothOpen.mixed_add`) and `FK (F_* + w) = FK F_* + FK w` (from
  `GalFields.Tail.FK_Fstar_add`, whose only hypothesis is the integrability of the `θ`-slice of
  `w`, supplied by `GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem` from
  `HQo α 4 w = SmoothOpen w ∧ HkMem α 4 w`).
* `N_tendsto_of_PhiTil` — the pointwise limit of `Construction.N`, stated with the slot
  convergence of `PhiTil α F Φ` itself (the repaired form of `N_tendsto`, avoiding the
  differentiability gap of `deriv_sub`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.N_tendsto
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.GalFields.Tail.FK_Fstar_add
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Pointwise convergence of the slots at a point of the open quadrant -/

/-- Uniform convergence on a set gives pointwise convergence at every point of the set. -/
theorem tendsto_at_of_tendstoUniformlyOn {ι β : Type*} {F : ι → β → ℝ} {f : β → ℝ}
    {l : Filter ι} {s : Set β} {x : β} (hx : x ∈ s) (h : TendstoUniformlyOn F f l s) :
    Tendsto (fun n => F n x) l (nhds (f x)) := by
  rw [Metric.tendstoUniformlyOn_iff] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rw [dist_comm]
  exact hn x hx

/-- **Pointwise slot convergence from local uniform convergence.**  If the slots
`mixed j i (f n)`, `j + i ≤ 1`, converge uniformly to those of `fl` on every compact subset of
the open quadrant, then at every `p ∈ Q0` the values at `p` converge.  (The compact tube around
`p` is the one used by `L12/linPart_tendsto`.) -/
theorem tendsto_mixed_at {f : ℕ → Fn} {fl : Fn} {p : ℝ × ℝ}
    (hp : p ∈ Work.FTS.EllipticEst.Q0)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ j i : ℕ, j + i ≤ 1 →
        TendstoUniformlyOn (fun n : ℕ => fun p : ℝ × ℝ =>
            Work.Spaces.mixed j i (f n) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i fl p.1 p.2) Filter.atTop K)
    (j i : ℕ) (hji : j + i ≤ 1) :
    Tendsto (fun n : ℕ => Work.Spaces.mixed j i (f n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i fl p.1 p.2)) := by
  obtain ⟨hz, hθ0, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  set K : Set (ℝ × ℝ) :=
    Set.Icc (p.1 / 2) (p.1 + 1) ×ˢ Set.Icc (p.2 / 2) ((p.2 + Real.pi / 2) / 2) with hK
  have hpK : p ∈ K := by
    rw [hK]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hKcomp : IsCompact K := by
    rw [hK]; exact isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    rw [hK] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨by linarith [hq1.1], by linarith [hq2.1], by linarith [hq2.2]⟩
  exact tendsto_at_of_tendstoUniformlyOn (β := ℝ × ℝ) (s := K) (x := p) hpK
    (hconv K hKcomp hKsub j i hji)

/-! ## The `F_*`-shift: mixed slots and the angular moment -/

/-- `F_*` is `C^∞` on the open quadrant. -/
theorem smoothOpen_Fstar (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
  Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)

/-- `SmoothOpen` is closed under sums. -/
theorem smoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at hf hg ⊢
  intro n
  exact (hf n).add (hg n)

/-- `Ftau α g τ = F_* + slice g τ` is `C^∞` on the open quadrant when the slice is. -/
theorem smoothOpen_Ftau {α : ℝ} {g : Fam} {τ : ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen (slice g τ)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftau α g τ) := by
  have h : Work.Construction.Ftau α g τ
      = fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ := rfl
  rw [h]
  exact smoothOpen_add (smoothOpen_Fstar α) hg

/-- **`F_*`-additivity of the mixed slots**: on the open quadrant, the mixed operators of the
profile `F = F_* + w` split into those of `F_*` and those of `w`. -/
theorem mixed_Fstar_add {α : ℝ} {w : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hw : Work.FTS.EllipticEst.SmoothOpen w) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => Work.Construction.Fstar α z θ + w z θ) z θ
      = Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ + Work.Spaces.mixed j i w z θ :=
  Work.FTS.EllipticEst.SmoothOpen.mixed_add (smoothOpen_Fstar α) hw j i z θ hz hθ.1 hθ.2

/-- The `θ`-slice of `w·K` is integrable on `Iθ` for `z > 0`, from `SmoothOpen w` and
`HkMem α 4 w` (the statement is `integrableOn_slice_of_SmoothOpen_HkMem` with the division by
`z` undone). -/
theorem integrableOn_slice_mul_K {α z : ℝ} {w : Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) (hwm : Work.Spaces.HkMem α 4 w) (hz : 0 < z) :
    IntegrableOn (fun θ => w z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have h := Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw hwm hz
  have h2 : IntegrableOn (fun θ => (Work.Spaces.K θ * w z θ / z) * z) Work.Spaces.Iθ :=
    h.mul_const z
  refine IntegrableOn.congr_fun h2 ?_ measurableSet_Icc
  intro θ _
  field_simp

/-- **`F_*`-additivity of the angular moment `FK`**, from the honest class `HQo α 4 w` of the
perturbation (no `GalClass` hypothesis is needed: only the integrability of the `θ`-slice of
`w·K`). -/
theorem FK_Fstar_add_of_SmoothOpen_HkMem {α : ℝ} {w : Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) (hwm : Work.Spaces.HkMem α 4 w) {z : ℝ}
    (hz : 0 < z) :
    Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + w z θ) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z :=
  Work.FTS.GalFields.Tail.FK_Fstar_add
    (fun z' hz' => integrableOn_slice_mul_K hw hwm hz') hz

/-! ## `sin (2θ) ≠ 0` on the open quadrant -/

/-- `sin (2θ) ≠ 0` for `θ ∈ (0, π/2)`: the quotient by `sin (2θ)` used to pass from the slot
`mixed 0 1 = D_θ` to the bare `∂_θ` is legitimate on the open quadrant. -/
theorem sin_two_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Real.sin (2 * θ) ≠ 0 := by
  have h1 : 0 < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-! ## The pointwise limit of `N` from the slots of `PhiTil` -/

/-- **The pointwise limit of `Construction.N`.**  `N α F Φ` is a scalar expression in the eight
quantities `F z θ`, `∂_θF(z,θ)`, `D_zF(z,θ)`, `FK F z`, `Φ̃(z,θ)`, `∂_zΦ̃(z,θ)`,
`∂_θΦ̃(z,θ)` with `Φ̃ = PhiTil α F Φ`; the hypotheses control the slots of `F` (order `≤ 1`),
`FK F z`, and the slots of `Φ̃` itself (order `≤ 1`) — which is exactly what the limit lemma
needs, since `Φ` enters `N` only through `PhiTil α F Φ`. -/
theorem N_tendsto_of_PhiTil {α : ℝ} {F : ℕ → Fn} {Fl : Fn} {Ψ : ℕ → Fn} {Ψl : Fn}
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Fl z θ)))
    (hFK : Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Fl z)))
    (hΨ : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.PhiTil α Fl Ψl) z θ))) :
    Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Ψ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Fl Ψl z θ)) := by
  have hsin := sin_two_ne_zero hθ
  -- the eight slots of the scalar expression `NNF`
  have hFZ : Tendsto (fun n : ℕ => F n z θ) Filter.atTop (nhds (Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hF 0 0 (by norm_num)
  have hFZD : Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  have hFTH' : Tendsto (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Real.sin (2 * θ) * Work.Spaces.pth Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  have hFTH : Tendsto (fun n : ℕ => Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.pth Fl z θ)) := by
    have h := hFTH'.const_mul (Real.sin (2 * θ))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hsin, one_mul] using h
  have hPZ : Tendsto (fun n : ℕ => Work.Spaces.pz
      (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pz (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
    have h : Tendsto (fun n : ℕ => z * Work.Spaces.pz
        (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (z * Work.Spaces.pz (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Work.Spaces.DthIter_zero, Work.Spaces.Dz] using hΨ 1 0 (by norm_num)
    have h2 := h.const_mul z⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hz), one_mul] using h2
  have hPTH : Tendsto (fun n : ℕ => Work.Spaces.pth
      (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pth (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
    have h : Tendsto (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth
        (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (Real.sin (2 * θ) * Work.Spaces.pth
          (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hΨ 0 1 (by norm_num)
    have h2 := h.const_mul (Real.sin (2 * θ))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hsin, one_mul] using h2
  have hP : Tendsto (fun n : ℕ => Work.Construction.PhiTil α (F n) (Ψ n) z θ) Filter.atTop
      (nhds (Work.Construction.PhiTil α Fl Ψl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hΨ 0 0 (by norm_num)
  have key := Work.FTS.StrongEps.NNF_tendsto (α := α) (z := z) (θ := θ)
    (FZ := Fl z θ) (FTH := Work.Spaces.pth Fl z θ) (FZD := Work.Spaces.Dz Fl z θ)
    (FKV := Work.Construction.FK Fl z)
    (P := Work.Construction.PhiTil α Fl Ψl z θ)
    (PZ := Work.Spaces.pz (Work.Construction.PhiTil α Fl Ψl) z θ)
    (PTH := Work.Spaces.pth (Work.Construction.PhiTil α Fl Ψl) z θ)
    hFZ hFTH hFZD hFK hP hPZ hPTH
  convert key using 1
  · funext n
    exact Work.FTS.StrongEps.N_eq_NNF α (F n) (Ψ n) z θ
  · congr 1

end Work.FTS.StrongEps.EpsWPLim
