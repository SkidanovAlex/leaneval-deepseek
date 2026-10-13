/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsWPLim/Gap.lean`

**The missing hypothesis of `epsWP_tendsto`: the jump of `λ = lamfun μ` at `μ = -1`.**

The conclusion of `epsWP_tendsto` unfolds (see `EpsWPLim.Main`) to the pointwise convergence of

`epsWP α ρ (ε n) Φs E (G n) s p = -𝓛_Γ^T(slice (JfamP ρ (ε n) (G n)) s)(p)
 + gRHS α (muDyn α (PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s)
     (lamDyn α (PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s) …`,

and every block of `gRHS` *except* the `Nstar` one converges from the hypotheses of the statement
(`EpsWPLim.gRHS_tendsto` proves this, with the convergence of the two modulation constants taken
separately).  The `Nstar` block needs

  `μ n + lamfun (μ n) + μ n·lamfun (μ n)  →  μ l + lamfun (μ l) + μ l·lamfun (μ l)`

where `μ n = muDyn α (PsiCan Φs E (JfamP ρ (ε n) (G n))) (JfamP ρ (ε n) (G n)) s` and
`μ l = muDyn α (PsiCan Φs E g) g s`, and the only hypothesis on `μ` is `hmu : μ n → μ l`.

That is **false**: `Nonlin.lamfun_add` gives `μ + lamfun μ + μ·lamfun μ = -μ` for `μ ≠ -1`, while
`lamfun (-1) = 0` (Lean's totalised division `-2·(-1)·(1+(-1))⁻¹ = 2·0 = 0`) gives `-1` at
`μ = -1`.  The coefficient of `D_z w` in `Nstar μ (lamfun μ) w` therefore **jumps by 2** at
`μ = -1`, and `Apriori.Nstar_lamfun` (`Nstar μ (lamfun μ) w = μ(D_z w − w)` for `μ ≠ -1`) fails
at `μ = -1`, where instead `Nstar (-1) 0 w = w + D_z w`.

`not_tendsto_Nstar_lamfun` below is the machine-checked witness of the failure of the missing
step, at the data `μ n = -1 + 1/(n+1) → -1`, `μ n ≠ -1`, `w = fun _ _ => z` (so that
`D_z w 1 0 = 1 ≠ 0`):

  `Nstar (μ n) (lamfun (μ n)) w 1 0 = μ n (1 − 1) = 0  →  0`, while
  `Nstar (-1) (lamfun (-1)) w 1 0 = 1·1 + 1·1 = 2`.

Hence `¬ Tendsto … (𝓝 (Nstar (-1) (lamfun (-1)) w 1 0))`.

Nothing in the hypotheses of `epsWP_tendsto` excludes this configuration: `hmu` only says that
`μ n → μ l`; `μ` is `mufunS α (N₀ α (F_τ + w n) (w n)) (N α (F_τ + w n) (Ψ n)) (w n)`, a
continuous functional of the slices `w n = slice (JfamP ρ (ε n) (G n)) s` and of the *arbitrary*
function `E : Fn → Fn` (through `Ψ n = slice Φs + E (w n)`), and no hypothesis bounds `μ` away
from `-1` (the only bound of the workspace, `Nonlin.mu_le_half`, needs the small ball
`Xn ≤ α^{7/4}`, `α ≤ α₄`).  The same jump is what made `EpsLocalP` and `rhsSlice_lipschitz_H4`
unprovable as stated (see `NOTES_session11.md` §9 and `NOTES_rhsSlice_lipschitz_H4_blocker.md`),
and the sibling statement `Submission/Work/FTS/StrongEps/gRHS_tendsto.lean` carries the
convergence of `λ` as its own hypothesis `hlam`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.StrongEps.EpsWPLim.Main
import Submission.Work.FTS.Nonlinear.Mu
import Submission.Work.FTS.Apriori.ZeroMode

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

/-! ## The jump of the coefficient `μ + λ + μλ` at `μ = -1` -/

/-- `lamfun (-1) = 0` by Lean's totalised division: `-2·(-1)/(1+(-1)) = 2·0⁻¹ = 0`. -/
theorem lamfun_neg_one : Work.Construction.lamfun (-1) = 0 := by
  simp only [Work.Construction.lamfun]
  norm_num

/-- At `μ = -1` the coefficient of `D_z w` in `Nstar μ (lamfun μ) w` is `-1`, while for
`μ ≠ -1` it is `-μ` (`Nonlin.lamfun_add`), whose limit at `-1` is `1`: the jump is `2`. -/
theorem coeff_neg_one :
    (-1 : ℝ) + Work.Construction.lamfun (-1) + (-1) * Work.Construction.lamfun (-1) = -1 := by
  rw [lamfun_neg_one]; norm_num

/-- The limit of the coefficient as `μ → -1` (`μ ≠ -1`) is `1 ≠ -1`. -/
theorem coeff_ne_neg_one (μ : ℝ) (hμ : μ ≠ -1) :
    μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ :=
  Work.FTS.Nonlin.lamfun_add hμ

/-! ## The missing step is false -/

/-- **The `Nstar` block cannot converge from `μ n → μ l` alone.**  With `μ n = -1 + 1/(n+1)`
(so `μ n → -1`, `μ n ≠ -1`) and the profile `w = fun _ _ => z`, every other slot of the `Nstar`
block is constant in `n`, yet the required identity fails: the left-hand side is constantly `0`
while the claimed limit is `2`. -/
theorem not_tendsto_Nstar_lamfun :
    ¬ Filter.Tendsto (fun n : ℕ => Work.Construction.Nstar ((-1 : ℝ) + 1 / (n + 1))
        (Work.Construction.lamfun ((-1 : ℝ) + 1 / (n + 1))) (fun z _ : ℝ => z) 1 0)
      Filter.atTop
      (nhds (Work.Construction.Nstar (-1) (Work.Construction.lamfun (-1))
        (fun z _ : ℝ => z) 1 0)) := by
  intro h
  -- the `n`-th value is `0`
  have hval : ∀ n : ℕ, Work.Construction.Nstar ((-1 : ℝ) + 1 / (n + 1))
      (Work.Construction.lamfun ((-1 : ℝ) + 1 / (n + 1))) (fun z _ : ℝ => z) 1 0 = 0 := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hμ : ((-1 : ℝ) + 1 / (n + 1)) ≠ -1 := by linarith
    rw [Work.FTS.Apriori.Nstar_lamfun hμ (fun z _ : ℝ => z)]
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show deriv (fun z : ℝ => z) 1 = 1 from by
      simpa using (hasDerivAt_id (1 : ℝ)).deriv]
    ring
  -- the limit value is `2`
  have hlim : Work.Construction.Nstar (-1) (Work.Construction.lamfun (-1))
      (fun z _ : ℝ => z) 1 0 = 2 := by
    simp only [Work.Construction.Nstar, lamfun_neg_one, Work.Spaces.Dz, Work.Spaces.pz]
    rw [show deriv (fun z : ℝ => z) 1 = 1 from by
      simpa using (hasDerivAt_id (1 : ℝ)).deriv]
    norm_num
  rw [funext hval, hlim] at h
  exact absurd (tendsto_nhds_unique tendsto_const_nhds h) (by norm_num)

/-! ## `lamfun` is continuous off `-1`: the two natural repairs of the statement -/

/-- **`lamfun` is continuous at every `μ ≠ -1`.**  Hence if the *limit* modulation constant is
`≠ -1`, the convergence of `λ` follows from the convergence of `μ`.
(`lamfun` is *not* continuous at `-1`: `lamfun (-1) = 0` while `lamfun μ → ∞` there.) -/
theorem tendsto_lamfun_of_ne {μ : ℕ → ℝ} {μl : ℝ}
    (hμ : Filter.Tendsto μ Filter.atTop (nhds μl)) (hl : μl ≠ -1) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.lamfun (μ n)) Filter.atTop
      (nhds (Work.Construction.lamfun μl)) := by
  have h1 : (1 : ℝ) + μl ≠ 0 := by
    intro h
    exact hl (by linarith)
  have hc : ContinuousAt (fun x : ℝ => (-2 * x) * (1 + x)⁻¹) μl :=
    (continuousAt_const.mul continuousAt_id).mul
      ((continuousAt_const.add continuousAt_id).inv₀ h1)
  have h := hc.tendsto.comp hμ
  simpa only [Work.Construction.lamfun, div_eq_mul_inv, Function.comp_def] using h

/-- **`epsWP_tendsto` with the single added hypothesis `muDyn α (PsiCan Φs E g) g s ≠ -1`.**

This is the minimal repair of the requested statement: from `hmu` (the convergence of `μ`) and
`muDyn α (PsiCan Φs E g) g s ≠ -1` the convergence of `λ = lamfun ∘ μ` follows by continuity
(`tendsto_lamfun_of_ne`), so that `EpsWPLim.epsWP_tendsto_of_lam` applies.  In the intended use
the hypothesis is supplied by `MuLamOK` (which gives `|muDyn| ≤ 1/2` on the class-`C` small
ball). -/
theorem epsWP_tendsto_of_ne_minus_one {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g : Fam} {ε : ℕ → ℝ} {G : ℕ → Fam} {s : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hQ : ∀ n : ℕ, Work.FTS.VocabO.HQo α 4
      (slice (JfamP ρ (ε n) (G n)) s))
    (hQg : Work.FTS.VocabO.HQo α 4 (slice g s))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 4 (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀)
    (hbg : Work.Spaces.HkNorm α 4 (slice g s) ≤ C₀)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ j i : ℕ, j + i ≤ 1 →
        TendstoUniformlyOn (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
            (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i (slice g s) p.1 p.2)
          Filter.atTop K)
    (hL12 : ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (slice (JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.L12 (slice g s) z)))
    (hL12T : Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f (Work.Coercivity.Transport
      (slice (JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport (slice g s)) 0)))
    (hFK : ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.FK
      (slice (JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.FK (slice g s) z)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)))
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n)))
      (JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hne : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s ≠ -1)
    (hmubar : Filter.Tendsto (fun n : ℕ => Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftau α
        (JfamP ρ (ε n) (G n)) s)
        (slice (JfamP ρ (ε n) (G n)) s))
      (Work.Construction.N α (Work.Construction.Ftau α
        (JfamP ρ (ε n) (G n)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s))) Filter.atTop
      (nhds (Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g s) (slice g s))
        (Work.Construction.N α (Work.Construction.Ftau α g s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)))))
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun n : ℕ => epsWP α ρ (ε n) Φs E (G n) s p.1 p.2)
      Filter.atTop (nhds (rhsFun α Φs E g s p.1 p.2)) :=
  epsWP_tendsto_of_lam hα hQ hQg hb hbg hconv hL12 hL12T hFK hTil hmu
    (tendsto_lamfun_of_ne hmu hne) hmubar hp

/-- **The repair in the form in which the workspace produces it.**  The modulation constant of the
scheme satisfies `|muDyn| ≤ 1/2` on the class-`C` small ball (`MuLamOK`, from
`Nonlin.mu_le_half`); with that bound at the *limit* datum the statement of `epsWP_tendsto`
(supplemented by it) holds. -/
theorem epsWP_tendsto_of_abs_le_half {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g : Fam} {ε : ℕ → ℝ} {G : ℕ → Fam} {s : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hQ : ∀ n : ℕ, Work.FTS.VocabO.HQo α 4
      (slice (JfamP ρ (ε n) (G n)) s))
    (hQg : Work.FTS.VocabO.HQo α 4 (slice g s))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 4 (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀)
    (hbg : Work.Spaces.HkNorm α 4 (slice g s) ≤ C₀)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ j i : ℕ, j + i ≤ 1 →
        TendstoUniformlyOn (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
            (slice (JfamP ρ (ε n) (G n)) s) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i (slice g s) p.1 p.2)
          Filter.atTop K)
    (hL12 : ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (slice (JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.L12 (slice g s) z)))
    (hL12T : Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f (Work.Coercivity.Transport
      (slice (JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport (slice g s)) 0)))
    (hFK : ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.FK
      (slice (JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.FK (slice g s) z)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)))
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n)))
      (JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hμb : |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s| ≤ 1 / 2)
    (hmubar : Filter.Tendsto (fun n : ℕ => Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftau α
        (JfamP ρ (ε n) (G n)) s)
        (slice (JfamP ρ (ε n) (G n)) s))
      (Work.Construction.N α (Work.Construction.Ftau α
        (JfamP ρ (ε n) (G n)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s))) Filter.atTop
      (nhds (Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g s) (slice g s))
        (Work.Construction.N α (Work.Construction.Ftau α g s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)))))
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun n : ℕ => epsWP α ρ (ε n) Φs E (G n) s p.1 p.2)
      Filter.atTop (nhds (rhsFun α Φs E g s p.1 p.2)) :=
  epsWP_tendsto_of_ne_minus_one hα hQ hQg hb hbg hconv hL12 hL12T hFK hTil hmu
    (by
      intro h
      rw [h] at hμb
      norm_num at hμb) hmubar hp

end Work.FTS.StrongEps.EpsWPLim
