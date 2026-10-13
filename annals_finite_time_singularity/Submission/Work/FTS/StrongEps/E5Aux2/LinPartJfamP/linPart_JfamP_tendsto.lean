import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux2.l12Slice_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.l12Transport_JfamP_tendsto
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.L12.linPart_tendsto_cont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `linPart_JfamP_tendsto` — convergence of the linear part along the `ε`-scheme

`linPart α f = -𝓛_Γ^T f` unfolds (definitionally) as

  `linPart α f z θ = -( f z θ + D_z f z θ - 2 f z θ/(1+z)
      - (2 z Γ(θ)/(c(1+z)²))·L₁₂(f)(z)
      - (3 D_θ f z θ/(1+z) - (Γ(θ)/c)(2z²/(1+z)³)·L₁₂(Transport f)(0)) )`.

So the convergence of `linPart α (slice (JfamP ρ (ε n) (G n)) s)` to
`linPart α (slice g s)` at a point `p` of the open quadrant follows from the convergence of
exactly five quantities:

* `f n p`, `D_z f n p`, `D_θ f n p` — the slots `(j,i) = (0,0), (1,0), (0,1)` at `p`, which are
  `mixed_JfamP_tendsto`;
* `L₁₂ (f n)(p.1)` — `l12Slice_JfamP_tendsto` (the dominated convergence theorem in the radial
  variable with the majorant `Maj σ/σ` of the `EpsDecay` clause);
* `L₁₂ (Transport (f n))(0)` — `l12Transport_JfamP_tendsto` (the same DCT, with the `θ`-DCT
  `l12dens_transport_tendsto_at` as its pointwise input).

All the coefficients are constants in `n`, so the assembly is the continuity of the arithmetic
operations (`linPart_tendsto_of_data`).

The `ℋ⁴`-norm route of `Work.FTS.StrongEps.L12.linPart_tendsto_cont` is *not* available here:
it needs a *uniform in `n`* bound `HkNorm α 4 (f n) ≤ B`, and no hypothesis of the statement
supplies one (the class clause and `EpsDecay` give `HkMem` and *first*-order slot bounds only).
The dominated-convergence route above avoids it entirely.
-/

namespace Work.FTS.StrongEps.E5Aux2.LinPartJfamP

set_option maxHeartbeats 1000000

/-- The pointwise unfolding of `linPart α f = -𝓛_Γ^T f`.  Purely definitional. -/
private lemma linPart_unfold (α : ℝ) (f : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    Work.FTS.StrongPersist.linPart α f z θ
      = -( f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z)
           - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
              * Work.Coercivity.L12f f z
           - (3 * Work.Spaces.Dth f z θ / (1 + z)
              - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
                 * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) := by
  simp only [Work.FTS.StrongPersist.linPart, Work.Coercivity.LGammaT, Work.Coercivity.LGamma,
    Work.Coercivity.L, Work.Coercivity.Proj, Work.Coercivity.Transport]

/-- **The abstract assembly**: if the five ingredients of `linPart` converge, then `linPart`
converges.  All coefficients are constants in `n`, so this is continuity of the arithmetic
operations. -/
private lemma linPart_tendsto_of_data {α : ℝ} {f : ℕ → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hf : Filter.Tendsto (fun n : ℕ => f n z θ) Filter.atTop (nhds (g z θ)))
    (hDz : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (f n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz g z θ)))
    (hDth : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dth (f n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dth g z θ)))
    (hL : Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f (f n) z) Filter.atTop
      (nhds (Work.Coercivity.L12f g z)))
    (hK : Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f
        (Work.Coercivity.Transport (f n)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.StrongPersist.linPart α (f n) z θ) Filter.atTop
      (nhds (Work.FTS.StrongPersist.linPart α g z θ)) := by
  set A : ℝ := 2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2) with hA
  set Bc : ℝ := (Work.Spaces.Gam α θ / Work.Spaces.c α)
    * (2 * z ^ 2 / (1 + z) ^ 3) with hBc
  have hinner : Filter.Tendsto (fun n : ℕ => f n z θ + Work.Spaces.Dz (f n) z θ
        - 2 * f n z θ / (1 + z)
        - A * Work.Coercivity.L12f (f n) z
        - (3 * Work.Spaces.Dth (f n) z θ / (1 + z)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport (f n)) 0))
      Filter.atTop (nhds (g z θ + Work.Spaces.Dz g z θ
        - 2 * g z θ / (1 + z)
        - A * Work.Coercivity.L12f g z
        - (3 * Work.Spaces.Dth g z θ / (1 + z)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))) :=
    ((((hf.add hDz).sub ((hf.const_mul 2).div_const (1 + z))).sub (hL.const_mul A)).sub
      (((hDth.const_mul 3).div_const (1 + z)).sub (hK.const_mul Bc)))
  have hfinal := hinner.neg
  have hfun : (fun n : ℕ => Work.FTS.StrongPersist.linPart α (f n) z θ)
      = fun n : ℕ => -(f n z θ + Work.Spaces.Dz (f n) z θ
        - 2 * f n z θ / (1 + z)
        - A * Work.Coercivity.L12f (f n) z
        - (3 * Work.Spaces.Dth (f n) z θ / (1 + z)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport (f n)) 0)) := by
    funext n
    rw [linPart_unfold α (f n) z θ, hA, hBc]
  have hlim : Work.FTS.StrongPersist.linPart α g z θ
      = -(g z θ + Work.Spaces.Dz g z θ
        - 2 * g z θ / (1 + z)
        - A * Work.Coercivity.L12f g z
        - (3 * Work.Spaces.Dth g z θ / (1 + z)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0)) := by
    rw [linPart_unfold α g z θ, hA, hBc]
  rw [hfun, hlim]
  exact hfinal

theorem linPart_JfamP_tendsto {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0)) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.FTS.StrongPersist.linPart α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2) Filter.atTop
        (nhds (Work.FTS.StrongPersist.linPart α (Work.FTS.Galerkin.slice g s) p.1 p.2)) := by
  intro p hp
  obtain ⟨hz, hθ0, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hp' : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ0, hθ2⟩
  -- the angular-regularity hypothesis in the shape `mixed_JfamP_tendsto` wants
  have hsm' : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n k => by simpa only [Work.FTS.StrongEps.Quad] using hsm n k
  -- the slot convergence of order `j + i ≤ 4` at `p`
  have hpt : ∀ j i : ℕ, j + i ≤ 1 → Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) p.1 p.2)) := by
    intro j i hji
    exact Work.FTS.StrongEps.mixed_JfamP_tendsto (τ := s) hρ hsm' hconv
      (fun n => (hε n).1) hε0 hl12 hp' (j := j) (i := i) (by omega)
  refine linPart_tendsto_of_data (α := α)
    (f := fun n : ℕ => Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (g := Work.FTS.Galerkin.slice g s) (z := p.1) (θ := p.2) ?_ ?_ ?_ ?_ ?_
  · -- the value `f n p → g p` (`(j,i) = (0,0)`)
    simpa only [Work.FTS.Galerkin.slice, Work.Spaces.mixed_zero_left,
      Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero]
      using hpt 0 0 (by norm_num)
  · -- the radial derivative `D_z (f n) p → D_z g p` (`(j,i) = (1,0)`)
    simpa only [Work.FTS.Galerkin.slice, Work.Spaces.mixed, Work.Spaces.DthIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
      using hpt 1 0 (by norm_num)
  · -- the angular derivative `D_θ (f n) p → D_θ g p` (`(j,i) = (0,1)`)
    simpa only [Work.FTS.Galerkin.slice, Work.Spaces.mixed, Work.Spaces.DthIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
      using hpt 0 1 (by norm_num)
  · -- the radial `L₁₂`-mode at `p.1 > 0` (`l12Slice_JfamP_tendsto`)
    have h := l12Slice_JfamP_tendsto hρ hα hε hε0 hsm hconv hC hMajint hDec hl12
      p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    simpa only [Work.FTS.Galerkin.slice, Work.Coercivity.L12f, Work.Construction.L12] using h
  · -- the zero mode of the transport block (`l12Transport_JfamP_tendsto`)
    simpa only [Work.FTS.Galerkin.slice] using
      l12Transport_JfamP_tendsto hρ hα hε hε0 hsm hconv hC hMajint hDec hl12

end Work.FTS.StrongEps.E5Aux2.LinPartJfamP
