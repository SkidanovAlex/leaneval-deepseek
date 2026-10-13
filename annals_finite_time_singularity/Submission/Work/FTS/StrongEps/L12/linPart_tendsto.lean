/-
# `linPart_tendsto`: local uniform convergence of `f n → g` gives convergence of `linPart`

`linPart α f = -𝓛_Γ^T f` decomposes as (all identities definitional)

  `linPart α f z θ = -(f + D_z f - 2f/(1+z)
      - (2zΓ(θ)/(c(1+z)²))·L₁₂(f)(z)
      - (3 D_θ f/(1+z) - (Γ(θ)/c)(2z²/(1+z)³)·L₁₂(Transport f)(0)))`.

At a point `p = (z,θ)` of the open quadrant every ingredient is one of

* a value of `mixed j i (f n)` with `j + i ≤ 1` (namely `(0,0)`, `(1,0)`, `(0,1)` for
  `f`, `D_z f`, `D_θ f`) — pointwise convergence comes from the hypothesis `hconv`
  (local uniform convergence on the compacts of `Q0`, and `p` lies in the compact box
  `[z/2, z+1] × [θ/2, (θ+π/2)/2] ⊆ Q0`);
* `L₁₂(f n)(z)` — convergence is `L12_tendsto_locUnif` (the `ε`-decomposition proof, using
  the uniform `ℋ⁴`-bound `B`);
* `L₁₂(Transport (f n))(0)` — this is exactly the hypothesis `hK0`.

Since all coefficients are constants in `n`, the conclusion follows from the continuity of
the arithmetic operations.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.L12.L12_tendsto_locUnif
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Pointwise convergence out of uniform convergence on a set: if `F n → f` uniformly on `s`
and `x ∈ s`, then `F n x → f x`. -/
private lemma tendsto_at_of_tendstoUniformlyOn {ι β : Type*} {F : ι → β → ℝ} {f : β → ℝ}
    {l : Filter ι} {s : Set β} {x : β} (hx : x ∈ s) (h : TendstoUniformlyOn F f l s) :
    Tendsto (fun n => F n x) l (nhds (f x)) := by
  rw [Metric.tendstoUniformlyOn_iff] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rw [dist_comm]
  exact hn x hx

/-- The pointwise unfolding of `linPart α f = -𝓛_Γ^T f` into the five values that the
convergence argument needs.  Purely definitional. -/
private lemma linPart_apply (α : ℝ) (f : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    Work.FTS.StrongPersist.linPart α f z θ
      = -( f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z)
           - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
              * Work.Coercivity.L12f f z
           - (3 * Work.Spaces.Dth f z θ / (1 + z)
              - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
                 * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) := by
  simp only [Work.FTS.StrongPersist.linPart, Work.Coercivity.LGammaT, Work.Coercivity.LGamma,
    Work.Coercivity.L, Work.Coercivity.Proj, Work.Coercivity.Transport]

theorem linPart_tendsto {α B : ℝ} {f : ℕ → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hmem : ∀ n : ℕ, Work.FTS.VocabO.HQo α 4 (f n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 4 (f n) ≤ B)
    (hmemg : Work.FTS.VocabO.HQo α 4 g) (hbg : Work.Spaces.HkNorm α 4 g ≤ B)
    (hconv : ∀ Km : Set (ℝ × ℝ), IsCompact Km → Km ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ j i : ℕ, j + i ≤ 1 →
        TendstoUniformlyOn (fun n p => Work.Spaces.mixed j i (f n) p.1 p.2)
          (fun p => Work.Spaces.mixed j i g p.1 p.2) Filter.atTop Km)
    (hK0 : Filter.Tendsto
      (fun n : ℕ => Work.Coercivity.L12f (Work.Coercivity.Transport (f n)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.FTS.StrongPersist.linPart α (f n) p.1 p.2)
        Filter.atTop (nhds (Work.FTS.StrongPersist.linPart α g p.1 p.2)) := by
  intro p hp
  obtain ⟨hz, hθ0, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  -- a compact box around `p` contained in the open quadrant
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
  -- pointwise convergence of every `mixed j i` with `j + i ≤ 1` at `p`
  have hpt : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n => Work.Spaces.mixed j i (f n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i g p.1 p.2)) :=
    fun j i hji =>
      tendsto_at_of_tendstoUniformlyOn (β := ℝ × ℝ) hpK (hconv K hKcomp hKsub j i hji)
  have hf0 : Tendsto (fun n => f n p.1 p.2) Filter.atTop (nhds (g p.1 p.2)) := by
    simpa using hpt 0 0 (by norm_num)
  have hDz : Tendsto (fun n => Work.Spaces.Dz (f n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.Dz g p.1 p.2)) := by
    simpa using hpt 1 0 (by norm_num)
  have hDth : Tendsto (fun n => Work.Spaces.Dth (f n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.Dth g p.1 p.2)) := by
    simpa using hpt 0 1 (by norm_num)
  -- the `L₁₂` of the datum, via `L12_tendsto_locUnif`
  have hb' : ∀ n, Work.FTS.Nonlin.Xn α (f n) ≤ B := fun n => hb n
  have hbg' : Work.FTS.Nonlin.Xn α g ≤ B := hbg
  have hconv' : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n zθ => f n zθ.1 zθ.2) (fun zθ => g zθ.1 zθ.2)
        Filter.atTop K := by
    intro Kc hKc hKQ
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hconv Kc hKc hKQ 0 0 (by norm_num)
  have hL12 : Tendsto (fun n => Work.Coercivity.L12f (f n) p.1) Filter.atTop
      (nhds (Work.Coercivity.L12f g p.1)) := by
    have h := Work.FTS.StrongEps.L12.L12_tendsto_locUnif α hα f g B hmem hb' hmemg hbg'
      hconv' p.1 (le_of_lt hz)
    simpa only [Work.Coercivity.L12f, Work.Construction.L12] using h
  -- the two `(z,θ)`-coefficients are constants in `n`
  set A : ℝ := 2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2) with hA
  set Bc : ℝ := (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
    * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) with hBc
  have hinner : Tendsto (fun n => f n p.1 p.2 + Work.Spaces.Dz (f n) p.1 p.2
        - 2 * f n p.1 p.2 / (1 + p.1)
        - A * Work.Coercivity.L12f (f n) p.1
        - (3 * Work.Spaces.Dth (f n) p.1 p.2 / (1 + p.1)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport (f n)) 0))
      Filter.atTop (nhds (g p.1 p.2 + Work.Spaces.Dz g p.1 p.2
        - 2 * g p.1 p.2 / (1 + p.1)
        - A * Work.Coercivity.L12f g p.1
        - (3 * Work.Spaces.Dth g p.1 p.2 / (1 + p.1)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))) := by
    refine ((((hf0.add hDz).sub ((hf0.const_mul 2).div_const (1 + p.1))).sub
      (hL12.const_mul A)).sub (((hDth.const_mul 3).div_const (1 + p.1)).sub
        (hK0.const_mul Bc)))
  have hfinal := hinner.neg
  have hfun : (fun n => Work.FTS.StrongPersist.linPart α (f n) p.1 p.2)
      = fun n => -(f n p.1 p.2 + Work.Spaces.Dz (f n) p.1 p.2
        - 2 * f n p.1 p.2 / (1 + p.1)
        - A * Work.Coercivity.L12f (f n) p.1
        - (3 * Work.Spaces.Dth (f n) p.1 p.2 / (1 + p.1)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport (f n)) 0)) := by
    funext n
    rw [linPart_apply α (f n) p.1 p.2, hA, hBc]
  have hlim : Work.FTS.StrongPersist.linPart α g p.1 p.2
      = -(g p.1 p.2 + Work.Spaces.Dz g p.1 p.2
        - 2 * g p.1 p.2 / (1 + p.1)
        - A * Work.Coercivity.L12f g p.1
        - (3 * Work.Spaces.Dth g p.1 p.2 / (1 + p.1)
            - Bc * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0)) := by
    rw [linPart_apply α g p.1 p.2, hA, hBc]
  rw [hfun, hlim]
  exact hfinal

end Work.FTS.StrongEps.L12
