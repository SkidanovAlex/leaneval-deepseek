import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_tendsto`: the pointwise limit of `Construction.N`, and the missing hypothesis

`Work.Construction.N α F Φ` is a *bare scalar expression* in the two profiles `F`, `Φ`: expanding
`Rop`, `Uop`, `Vop` and `PhiTil` it only depends on `F`, `Φ` through the eight scalars

`F z θ`, `∂_θF(z,θ)`, `D_zF(z,θ)`, `FK F z`, `Φ̃(z,θ)`, `∂_zΦ̃(z,θ)`, `∂_θΦ̃(z,θ)`,
with `Φ̃ = PhiTil α F Φ`.

Hence, whenever the eight corresponding sequences converge, `N α (F n) (Φ n) z θ` converges to
`N α Flim Φlim z θ` — the content of `NNF_tendsto` below, used to prove the *repaired* statement
`N_tendsto_of_pz_pth`.

**The requested statement `N_tendsto` is FALSE as written** (see the module
`Submission/Work/FTS/StrongEps/NOTES_N_tendsto_FALSE.md` for the counterexample, and
`N_tendsto_of_pz_pth` for the repair): its hypotheses control
`∂_z(F n z'↦…)` and `∂_z(L₁₂(F n))` at `z` *separately*, but `N` contains
`∂_zΦ̃(z,θ) = ∂_z(Φ - (1/(4α)) sin(2θ)·L₁₂(F))(z,θ)`, and the identity
`deriv (f - c·g) z = deriv f z - c·deriv g z` **needs** `f` and `g` to be differentiable at `z`
(`deriv_sub`).  If one of them is not (e.g. a kinked `z`-slice), the two sides genuinely differ,
and the data of the hypotheses does not force differentiability.  The two extra convergence
hypotheses `hPz`, `hPth` of `N_tendsto_of_pz_pth` (convergence of `∂_zΦ̃`, `∂_θΦ̃` themselves)
are exactly what is missing.
-/

namespace Work.FTS.StrongEps

open scoped Real
open Filter

set_option autoImplicit false

noncomputable section

/-- The scalar expression of `N α F Φ z θ`: `fz = F z θ`, `fth = ∂_θF(z,θ)`, `fzD = D_zF(z,θ)`,
`fkv = FK F z`, `pv = Φ̃(z,θ)`, `pzv = ∂_zΦ̃(z,θ)`, `pthv = ∂_θΦ̃(z,θ)` with
`Φ̃ = PhiTil α F Φ`.  It is `rfl`-equal to `N α F Φ z θ` (`N_eq_NNF`). -/
def NNF (α z θ fz fth fzD fkv pv pzv pthv : ℝ) : ℝ :=
  2 * ((2 * Real.sin θ * pv + α * Real.sin θ * z * pzv + Real.cos θ * pthv) / Real.cos θ) * fz
    - 2 * (-3 * pv - α * z * pzv) * fth
    - 2 * α * (pthv - Real.tan θ * pv) * fzD
    - (1 / 2) * Real.sin (2 * θ) * fkv * fth
    - Real.sin θ ^ 2 * fkv * fz

theorem N_eq_NNF (α : ℝ) (F Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.N α F Φ z θ
      = NNF α z θ (F z θ) (Work.Spaces.pth F z θ) (Work.Spaces.Dz F z θ)
          (Work.Construction.FK F z)
          (Work.Construction.PhiTil α F Φ z θ)
          (Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z θ)
          (Work.Spaces.pth (Work.Construction.PhiTil α F Φ) z θ) := by
  simp only [Work.Construction.N, Work.Construction.Rop, Work.Construction.Uop,
    Work.Construction.Vop, Work.Construction.s2, NNF]

/-- `NNF` is continuous in its eight scalar arguments, hence preserves limits. -/
theorem NNF_tendsto {α z θ FZ FTH FZD FKV P PZ PTH : ℝ}
    {fz fth fzD fkv pv pzv pthv : ℕ → ℝ}
    (h1 : Filter.Tendsto fz Filter.atTop (nhds FZ))
    (h2 : Filter.Tendsto fth Filter.atTop (nhds FTH))
    (h3 : Filter.Tendsto fzD Filter.atTop (nhds FZD))
    (h4 : Filter.Tendsto fkv Filter.atTop (nhds FKV))
    (h5 : Filter.Tendsto pv Filter.atTop (nhds P))
    (h6 : Filter.Tendsto pzv Filter.atTop (nhds PZ))
    (h7 : Filter.Tendsto pthv Filter.atTop (nhds PTH)) :
    Filter.Tendsto
      (fun n : ℕ => NNF α z θ (fz n) (fth n) (fzD n) (fkv n) (pv n) (pzv n) (pthv n))
      Filter.atTop (nhds (NNF α z θ FZ FTH FZD FKV P PZ PTH)) := by
  have hR : Filter.Tendsto
      (fun n : ℕ => (2 * Real.sin θ * pv n + α * Real.sin θ * z * pzv n + Real.cos θ * pthv n)
        / Real.cos θ) Filter.atTop
      (nhds ((2 * Real.sin θ * P + α * Real.sin θ * z * PZ + Real.cos θ * PTH)
        / Real.cos θ)) :=
    (((h5.const_mul (2 * Real.sin θ)).add (h6.const_mul (α * Real.sin θ * z))).add
      (h7.const_mul (Real.cos θ))).div_const (Real.cos θ)
  have hU : Filter.Tendsto (fun n : ℕ => -3 * pv n - α * z * pzv n) Filter.atTop
      (nhds (-3 * P - α * z * PZ)) :=
    (h5.const_mul (-3)).sub (h6.const_mul (α * z))
  have hV : Filter.Tendsto (fun n : ℕ => pthv n - Real.tan θ * pv n) Filter.atTop
      (nhds (PTH - Real.tan θ * P)) := h7.sub (h5.const_mul (Real.tan θ))
  have hB1 := (hR.const_mul 2).mul h1
  have hB2 := (hU.const_mul 2).mul h2
  have hB3 := (hV.const_mul (2 * α)).mul h3
  have hB4 := (h4.const_mul ((1 / 2) * Real.sin (2 * θ))).mul h2
  have hB5 := (h4.const_mul (Real.sin θ ^ 2)).mul h1
  simpa only [NNF] using (((hB1.sub hB2).sub hB3).sub hB4).sub hB5

/-- **The repaired limit lemma.**  Same hypotheses as `N_tendsto`, plus the two *missing* slot
convergences: the `z`- and `θ`-derivatives of `PhiTil α (F n) (Φ n)` at `(z,θ)` converge to those
of `PhiTil α Flim Φlim`.  (They are what the identities `deriv_sub`/`deriv_const_sub` would
provide from the other hypotheses once the relevant slices are differentiable.)  With them the
statement is a limit computation, carried out by `NNF_tendsto` via `N_eq_NNF`. -/
theorem N_tendsto_of_pz_pth {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Flim : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → Work.FTS.Galerkin.Fn} {Φlim : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hΦ : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Φ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Φlim z θ)))
    (hlF : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (F n) z) Filter.atTop
      (nhds (Work.Construction.L12 Flim z)))
    (hdF : Filter.Tendsto (fun n : ℕ => deriv (fun z' : ℝ => Work.Construction.L12 (F n) z') z)
      Filter.atTop
      (nhds (deriv (fun z' : ℝ => Work.Construction.L12 Flim z') z)))
    (hFK : Filter.Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Flim z)))
    (hPz : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.pz (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pz (Work.Construction.PhiTil α Flim Φlim) z θ)))
    (hPth : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.pth (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pth (Work.Construction.PhiTil α Flim Φlim) z θ))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Flim Φlim z θ)) := by
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hF0 : Filter.Tendsto (fun n : ℕ => F n z θ) Filter.atTop (nhds (Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hF 0 0 (by norm_num)
  have hFDz : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  have hFth' : Filter.Tendsto (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ)
      Filter.atTop (nhds (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  have hFth : Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.pth Flim z θ)) := by
    have h := hFth'.const_mul (Real.sin (2 * θ))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hsin, one_mul] using h
  have hΦ0 : Filter.Tendsto (fun n : ℕ => Φ n z θ) Filter.atTop (nhds (Φlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hΦ 0 0 (by norm_num)
  have hPval : Filter.Tendsto (fun n : ℕ => Work.Construction.PhiTil α (F n) (Φ n) z θ)
      Filter.atTop (nhds (Work.Construction.PhiTil α Flim Φlim z θ)) := by
    have h := hΦ0.sub (hlF.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    simpa only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2] using h
  have key := NNF_tendsto (α := α) (z := z) (θ := θ)
    (FZ := Flim z θ) (FTH := Work.Spaces.pth Flim z θ) (FZD := Work.Spaces.Dz Flim z θ)
    (FKV := Work.Construction.FK Flim z)
    (P := Work.Construction.PhiTil α Flim Φlim z θ)
    (PZ := Work.Spaces.pz (Work.Construction.PhiTil α Flim Φlim) z θ)
    (PTH := Work.Spaces.pth (Work.Construction.PhiTil α Flim Φlim) z θ)
    hF0 hFth hFDz hFK hPval hPz hPth
  convert key using 1
  · funext n
    exact N_eq_NNF α (F n) (Φ n) z θ
  · congr 1

/-- `θ' ↦ sin(2θ')` is differentiable. -/
theorem differentiableAt_sin_two (θ : ℝ) :
    DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ :=
  ((Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).differentiableAt

/-- `deriv (sin (2·)) θ = 2 cos (2θ)`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  simpa [Function.comp_def, mul_comm] using h

/-- **The repaired limit lemma, differentiability form.**  Same hypotheses as `N_tendsto`, plus the
differentiability, at `z` (resp. `θ`), of the `z`-slices (resp. `θ`-slices) of `Φ n` and of
`L₁₂(F n)`, for every `n` and for the limit — what a caller holding smooth profiles has.  From
these the two missing `PhiTil`-slot convergences follow by `deriv_sub`, and
`N_tendsto_of_pz_pth` applies. -/
theorem N_tendsto_of_diff {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Flim : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → Work.FTS.Galerkin.Fn} {Φlim : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hΦ : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Φ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Φlim z θ)))
    (hlF : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (F n) z) Filter.atTop
      (nhds (Work.Construction.L12 Flim z)))
    (hdF : Filter.Tendsto (fun n : ℕ => deriv (fun z' : ℝ => Work.Construction.L12 (F n) z') z)
      Filter.atTop
      (nhds (deriv (fun z' : ℝ => Work.Construction.L12 Flim z') z)))
    (hFK : Filter.Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Flim z)))
    (hdz : ∀ n : ℕ, DifferentiableAt ℝ (fun z' : ℝ => Φ n z' θ) z)
    (hLz : ∀ n : ℕ, DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.L12 (F n) z') z)
    (hdzl : DifferentiableAt ℝ (fun z' : ℝ => Φlim z' θ) z)
    (hLzl : DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.L12 Flim z') z)
    (hth : ∀ n : ℕ, DifferentiableAt ℝ (fun θ' : ℝ => Φ n z θ') θ)
    (hthl : DifferentiableAt ℝ (fun θ' : ℝ => Φlim z θ') θ) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Flim Φlim z θ)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  -- the `∂_z Φ̃`-identity
  have hpz_gen : ∀ (G' Φ' : ℝ → ℝ → ℝ),
      DifferentiableAt ℝ (fun z' : ℝ => Φ' z' θ) z →
      DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.L12 G' z') z →
      Work.Spaces.pz (Work.Construction.PhiTil α G' Φ') z θ
        = Work.Spaces.pz Φ' z θ - (1 / (4 * α)) * Real.sin (2 * θ)
            * deriv (fun z' : ℝ => Work.Construction.L12 G' z') z := by
    intro G' Φ' hd hL
    rw [show Work.Spaces.pz (Work.Construction.PhiTil α G' Φ') z θ
        = deriv (fun z' : ℝ => Work.Construction.PhiTil α G' Φ' z' θ) z from rfl,
      show Work.Spaces.pz Φ' z θ = deriv (fun z' : ℝ => Φ' z' θ) z from rfl]
    have hcd : DifferentiableAt ℝ
        (fun z' : ℝ => ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 G' z') z :=
      hL.const_mul _
    have hfun : (fun z' : ℝ => Work.Construction.PhiTil α G' Φ' z' θ)
        = (fun z' : ℝ => Φ' z' θ
            - ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 G' z') := by
      funext z'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    rw [hfun]
    have hsplit : (fun z' : ℝ => Φ' z' θ
          - ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Construction.L12 G' z')
        = (fun z' : ℝ => Φ' z' θ)
          - (fun z' : ℝ => ((1 / (4 * α)) * Real.sin (2 * θ))
              * Work.Construction.L12 G' z') := rfl
    rw [hsplit, deriv_sub hd hcd, deriv_const_mul _ hL]
  -- the `∂_θ Φ̃`-identity
  have hpth_gen : ∀ (F' Φ' : ℝ → ℝ → ℝ),
      DifferentiableAt ℝ (fun θ' : ℝ => Φ' z θ') θ →
      Work.Spaces.pth (Work.Construction.PhiTil α F' Φ') z θ
        = Work.Spaces.pth Φ' z θ - (1 / (4 * α)) * Work.Construction.L12 F' z
            * (2 * Real.cos (2 * θ)) := by
    intro F' Φ' hd
    rw [show Work.Spaces.pth (Work.Construction.PhiTil α F' Φ') z θ
        = deriv (fun θ' : ℝ => Work.Construction.PhiTil α F' Φ' z θ') θ from rfl,
      show Work.Spaces.pth Φ' z θ = deriv (fun θ' : ℝ => Φ' z θ') θ from rfl]
    have hcd : DifferentiableAt ℝ
        (fun θ' : ℝ => ((1 / (4 * α)) * Work.Construction.L12 F' z) * Real.sin (2 * θ')) θ :=
      (differentiableAt_sin_two θ).const_mul _
    have hfun : (fun θ' : ℝ => Work.Construction.PhiTil α F' Φ' z θ')
        = (fun θ' : ℝ => Φ' z θ'
            - ((1 / (4 * α)) * Work.Construction.L12 F' z) * Real.sin (2 * θ')) := by
      funext θ'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [hfun]
    have hsplit : (fun θ' : ℝ => Φ' z θ'
          - ((1 / (4 * α)) * Work.Construction.L12 F' z) * Real.sin (2 * θ'))
        = (fun θ' : ℝ => Φ' z θ')
          - (fun θ' : ℝ => ((1 / (4 * α)) * Work.Construction.L12 F' z)
              * Real.sin (2 * θ')) := rfl
    rw [hsplit, deriv_sub hd hcd, deriv_const_mul _ (differentiableAt_sin_two θ),
      (hasDerivAt_sin_two θ).deriv]
  -- the two missing convergences
  have hpz_eq : ∀ Φ' : ℝ → ℝ → ℝ,
      Work.Spaces.pz Φ' z θ = Work.Spaces.mixed 1 0 Φ' z θ / z := by
    intro Φ'
    rw [show Work.Spaces.mixed 1 0 Φ' z θ = z * Work.Spaces.pz Φ' z θ from rfl]
    field_simp
  have hpth_eq : ∀ Φ' : ℝ → ℝ → ℝ,
      Work.Spaces.pth Φ' z θ = Work.Spaces.mixed 0 1 Φ' z θ / Real.sin (2 * θ) := by
    intro Φ'
    rw [show Work.Spaces.mixed 0 1 Φ' z θ
        = Real.sin (2 * θ) * Work.Spaces.pth Φ' z θ from rfl]
    field_simp
  have hPz : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.pz (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pz (Work.Construction.PhiTil α Flim Φlim) z θ)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => Work.Spaces.pz (Φ n) z θ) Filter.atTop
        (nhds (Work.Spaces.pz Φlim z θ)) := by
      have h := (hΦ 1 0 (by norm_num)).div_const z
      rw [show (fun n : ℕ => Work.Spaces.mixed 1 0 (Φ n) z θ / z)
            = (fun n : ℕ => Work.Spaces.pz (Φ n) z θ) from funext fun n => (hpz_eq (Φ n)).symm,
        show Work.Spaces.mixed 1 0 Φlim z θ / z = Work.Spaces.pz Φlim z θ from (hpz_eq Φlim).symm]
        at h
      exact h
    have h2 : Filter.Tendsto (fun n : ℕ => Work.Spaces.pz (Φ n) z θ
        - (1 / (4 * α)) * Real.sin (2 * θ)
            * deriv (fun z' : ℝ => Work.Construction.L12 (F n) z') z) Filter.atTop
        (nhds (Work.Spaces.pz Φlim z θ - (1 / (4 * α)) * Real.sin (2 * θ)
            * deriv (fun z' : ℝ => Work.Construction.L12 Flim z') z)) :=
      h1.sub (hdF.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    convert h2 using 1
    · funext n
      exact hpz_gen (F n) (Φ n) (hdz n) (hLz n)
    · congr 1
      exact hpz_gen Flim Φlim hdzl hLzl
  have hPth : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.pth (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pth (Work.Construction.PhiTil α Flim Φlim) z θ)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (Φ n) z θ) Filter.atTop
        (nhds (Work.Spaces.pth Φlim z θ)) := by
      have h := (hΦ 0 1 (by norm_num)).div_const (Real.sin (2 * θ))
      rw [show (fun n : ℕ => Work.Spaces.mixed 0 1 (Φ n) z θ / Real.sin (2 * θ))
            = (fun n : ℕ => Work.Spaces.pth (Φ n) z θ) from funext fun n => (hpth_eq (Φ n)).symm,
        show Work.Spaces.mixed 0 1 Φlim z θ / Real.sin (2 * θ) = Work.Spaces.pth Φlim z θ from
          (hpth_eq Φlim).symm] at h
      exact h
    have h2 : Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (Φ n) z θ
        - (1 / (4 * α)) * Work.Construction.L12 (F n) z * (2 * Real.cos (2 * θ))) Filter.atTop
        (nhds (Work.Spaces.pth Φlim z θ - (1 / (4 * α)) * Work.Construction.L12 Flim z
            * (2 * Real.cos (2 * θ)))) := by
      have h2' : Filter.Tendsto (fun n : ℕ => ((1 / (4 * α)) * (2 * Real.cos (2 * θ)))
          * Work.Construction.L12 (F n) z) Filter.atTop
          (nhds (((1 / (4 * α)) * (2 * Real.cos (2 * θ))) * Work.Construction.L12 Flim z)) :=
        hlF.const_mul _
      convert h1.sub h2' using 1
      · funext n; ring
      · ring
    convert h2 using 1
    · funext n
      exact hpth_gen (F n) (Φ n) (hth n)
    · congr 1
      exact hpth_gen Flim Φlim hthl
  exact N_tendsto_of_pz_pth hz hθ hF hΦ hlF hdF hFK hPz hPth

theorem N_tendsto {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Flim : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → Work.FTS.Galerkin.Fn} {Φlim : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hΦ : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Φ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Φlim z θ)))
    (hlF : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (F n) z) Filter.atTop
      (nhds (Work.Construction.L12 Flim z)))
    (hdF : Filter.Tendsto (fun n : ℕ => deriv (fun z' : ℝ => Work.Construction.L12 (F n) z') z)
      Filter.atTop
      (nhds (deriv (fun z' : ℝ => Work.Construction.L12 Flim z') z)))
    (hFK : Filter.Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Flim z))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Flim Φlim z θ)) := by sorry

end

end Work.FTS.StrongEps
