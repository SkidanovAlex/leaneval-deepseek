import Mathlib.Topology.Algebra.Ring.Real
import Submission.Work.FTS.StrongEps.E5Aux2.l12Transport_JfamP_tendsto
import Submission.Work.Construction.MufunS
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-zero-mode `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` of the `E5` extraction

The dynamic modulation constant of the fake-time equation is the **corrected** constant
`Galerkin.muDyn = Construction.mufunS` (the sign fix of `FTS_MUFUN_SIGN.md` §5, option (a′)),
which by construction satisfies (`Construction.two_mul_mufunS`, with `μ̄ = Construction.mubar`)

  `2α·muDyn α Φ g τ = μ̄(N₀, N) + L₁₂(Transport g(τ))(0)`.

Inverting this relation expresses the paper's zero-mode functional `μ̄` as

  `μ̄ = 2α·muDyn − L₁₂(Transport g(τ))(0)`,

a **difference of the two quantities that the hypotheses of the `E5` extraction already make
converge**: `Work.FTS.StrongEps.E5Aux2.muDyn_tendsto` (`hmu`) for the first summand and
`Work.FTS.StrongEps.E5Aux2.l12Transport_JfamP_tendsto` (`hL12T`) for the second.  Hence
`μ̄(N₀(P₀J_εG_n), N(P₀J_εG_n, PsiCan(P₀J_εG_n))) → μ̄(N₀(g), N(g, PsiCan g))` at every
fixed `s`, with no further hypothesis — this is the content of `mubar_JfamP_tendsto`.

The only structural input is the invertibility of `2α` (`α ∈ (0,1]`), which is why the
statement carries `hα : α ∈ Set.Ioc 0 1` even though the convergence itself is insensitive to
the value of `α`.
-/

namespace Work.FTS.StrongEps.E5Aux2.MubarJfamP

/-- **The defining relation of the modulation constant, solved for `μ̄`**:

  `μ̄(N₀(F_*+g(τ)), N(F_*+g(τ), Φ(τ))) = 2α·muDyn α Φ g τ − L₁₂(Transport g(τ))(0)`.

This is `Construction.two_mul_mufunS` (`2α·mufunS = μ̄ + L₁₂(Transport g)(0)`) with
`Galerkin.muDyn` unfolded once to `mufunS`, i.e. `MeridianDyn.two_mul_muDyn` rearranged, with
`L₁₂ = Coercivity.L12f` (definitionally the same functional). -/
theorem mubar_eq_two_mul_muDyn {α : ℝ} (hα : α ≠ 0) (Φ g : Work.FTS.Galerkin.Fam) (τ : ℝ) :
    Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice g τ))
        (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
      = 2 * α * Work.FTS.Galerkin.muDyn α Φ g τ
        - Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g τ)) 0 := by
  -- the defining relation, in the form `2α·muDyn = μ̄ + L₁₂(Transport g)(0)`
  have hmu : 2 * α * Work.FTS.Galerkin.muDyn α Φ g τ
      = Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice g τ))
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
        + Work.Construction.L12 (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g τ)) 0 := by
    have h2 := Work.Construction.two_mul_mufunS α
      (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice g τ))
      (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
      (Work.FTS.Galerkin.slice g τ) hα
    rw [Work.FTS.Galerkin.muDyn]
    exact h2
  -- `Construction.L12` and `Coercivity.L12f` are the same functional
  have hL12 : Work.Construction.L12 (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g τ)) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g τ)) 0 := rfl
  rw [hL12] at hmu
  linarith

theorem mubar_JfamP_tendsto {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hL12T : Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f
      (Work.Coercivity.Transport (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0)
      Filter.atTop (nhds (Work.Coercivity.L12f
        (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s)) 0))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
        (Work.Construction.N α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))) Filter.atTop
      (nhds (Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g s) (Work.FTS.Galerkin.slice g s))
        (Work.Construction.N α (Work.Construction.Ftau α g s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s)))) := by
  -- `α ≠ 0`, so that the defining relation of `μ̄` can be inverted
  have hα0 : α ≠ 0 := by
    have h := hα.1
    linarith
  -- the pointwise identity expressing `μ̄` as `2α·muDyn − L₁₂(Transport g)(0)`
  have hkey : ∀ n : ℕ, Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
        (Work.Construction.N α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))
      = 2 * α * Work.FTS.Galerkin.muDyn α
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s
        - Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0 :=
    fun n => mubar_eq_two_mul_muDyn hα0 _ _ s
  have hkeylim : Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g s) (Work.FTS.Galerkin.slice g s))
        (Work.Construction.N α (Work.Construction.Ftau α g s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s))
      = 2 * α * Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s
        - Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s)) 0 :=
    mubar_eq_two_mul_muDyn hα0 _ _ s
  -- the difference of the two convergent families
  have hmain : Filter.Tendsto (fun n : ℕ => 2 * α * Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s
      - Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (2 * α * Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s
      - Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s)) 0)) :=
    (hmu.const_mul (2 * α)).sub hL12T
  simpa only [hkey, hkeylim] using hmain

end Work.FTS.StrongEps.E5Aux2.MubarJfamP
