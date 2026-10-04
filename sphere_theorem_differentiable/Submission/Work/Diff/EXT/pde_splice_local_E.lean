import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.pde_defs
import Submission.Work.Diff.EXT.pde_splice
import Submission.Work.Diff.EXT.gen.Basic
import Submission.Work.Diff.EXT.gen.AseqG_eq_PsiG
import Submission.Work.Diff.EXT.gen.Hyperplane
import Submission.Work.Diff.EXT.gen.JetSmooth
import Submission.Work.Diff.EXT.gen.FlatJets
import Submission.Work.Diff.EXT.gen.FlatE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local splicing of two solutions of a quasilinear parabolic system (`MatE`-valued)

The target theorem of this file: two `C^∞` functions `u`, `v : ℝ × E → MatE` solving the same
quasilinear system `∂ₜ w = Φ(·, J w)` (with `J` the *spatial* `2`-jet) on an open set `B`, on the
two sides of a hyperplane `{t = T}`, and with equal `t = T` slices near `y₀`, splice to a `C^∞`
function at `(T, y₀)`.

The proof follows `Submission/Work/Diff/EXT/pde_splice.lean` (the global, `ℝⁿ`-valued version),
using the generic (`E`, `F` arbitrary, open-set) lemmas of `Submission/Work/Diff/EXT/gen/`.
-/

open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT

theorem pde_splice_local_E
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {T : ℝ} {y₀ : E} {B : Set (ℝ × E)} (hB : IsOpen B) (hB₀ : (T, y₀) ∈ B)
    (Φ : E × (Work.Diff.EXT.MatE (E := E) × (E →L[ℝ] Work.Diff.EXT.MatE (E := E)) ×
        (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E))) → Work.Diff.EXT.MatE (E := E))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {u v : ℝ × E → Work.Diff.EXT.MatE (E := E)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v B)
    (huS : ∀ z ∈ B, z.1 < T →
      deriv (fun s => u (s, z.2)) z.1 = Φ (z.2, Work.Diff.EXT.jet2 u z))
    (hvS : ∀ z ∈ B, T < z.1 →
      deriv (fun s => v (s, z.2)) z.1 = Φ (z.2, Work.Diff.EXT.jet2 v z))
    (hslice : (fun y => u (T, y)) =ᶠ[nhds y₀] (fun y => v (T, y))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => if p.1 ≤ T then u p else v p) (T, y₀) := by
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.mp hB (T, y₀) hB₀
  -- a ball around the seam, contained in `B`
  set V : Set (ℝ × E) := Metric.ball (T, y₀) ρ with hVdef
  have hVopen : IsOpen V := by rw [hVdef]; exact Metric.isOpen_ball
  have hTV : (T, y₀) ∈ V := by rw [hVdef, Metric.mem_ball]; simpa using hρ
  have hVB : V ⊆ B := by
    intro q hq
    rw [hVdef] at hq
    exact hρB hq
  have huV : ContDiffOn ℝ (⊤ : ℕ∞) u V := hu.mono hVB
  have hvV : ContDiffOn ℝ (⊤ : ℕ∞) v V := hv.mono hVB
  -- smoothness of the whole jet/sequence machinery on `V`
  obtain ⟨hsJet_u, htderiv_u, hAseq_u, hSeq_u, hsJetSeq_u, hPsi, hPsiComp_u⟩ :=
    Work.Diff.EXT.gen.contDiffOn_jet_sequence (E := E) (F := MatE (E := E)) hVopen Φ hΦ huV
  obtain ⟨-, -, hAseq_v, hSeq_v, hsJetSeq_v, -, hPsiComp_v⟩ :=
    Work.Diff.EXT.gen.contDiffOn_jet_sequence (E := E) (F := MatE (E := E)) hVopen Φ hΦ hvV
  have hclair : ∀ (g : ℝ × E → MatE (E := E)), ContDiffOn ℝ (⊤ : ℕ∞) g V →
      ∀ z ∈ V, deriv (fun s => sJetG g (s, z.2)) z.1 = sJetG (tderivG g) z :=
    fun g hg z hz => Work.Diff.EXT.gen.deriv_sJetG hVopen hg hz
  -- the two open half-spaces of `V`
  have hS1 : ∀ z ∈ (V ∩ {z : ℝ × E | z.1 < T}), (V ∩ {z : ℝ × E | z.1 < T}) ∈ nhds z :=
    fun z hz => (hVopen.inter (isOpen_lt continuous_fst continuous_const)).mem_nhds hz
  have hS2 : ∀ z ∈ (V ∩ {z : ℝ × E | T < z.1}), (V ∩ {z : ℝ × E | T < z.1}) ∈ nhds z :=
    fun z hz => (hVopen.inter (isOpen_lt continuous_const continuous_fst)).mem_nhds hz
  have hPDE_u : ∀ z ∈ V ∩ {z : ℝ × E | z.1 < T},
      deriv (fun s => u (s, z.2)) z.1 = Φ (z.2, sJetG u z) := by
    intro z hz
    have h := huS z (hVB hz.1) hz.2
    rwa [show Work.Diff.EXT.jet2 u z = Work.Diff.EXT.sJetG u z from rfl] at h
  have hPDE_v : ∀ z ∈ V ∩ {z : ℝ × E | T < z.1},
      deriv (fun s => v (s, z.2)) z.1 = Φ (z.2, sJetG v z) := by
    intro z hz
    have h := hvS z (hVB hz.1) hz.2
    rwa [show Work.Diff.EXT.jet2 v z = Work.Diff.EXT.sJetG v z from rfl] at h
  -- the recursion and the identification of `AseqG` with the time derivatives, inside each
  -- half-space
  have hrec_u : ∀ j : ℕ, ∀ z ∈ V ∩ {z : ℝ × E | z.1 < T},
      AseqG Φ u j z = PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ u i) z) :=
    fun j => Work.Diff.EXT.gen.AseqG_eq_PsiG Φ hVopen (fun z hz => hz.1) hS1 hPDE_u hSeq_u
      hsJetSeq_u hPsi hclair j
  have hrec_v : ∀ j : ℕ, ∀ z ∈ V ∩ {z : ℝ × E | T < z.1},
      AseqG Φ v j z = PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ v i) z) :=
    fun j => Work.Diff.EXT.gen.AseqG_eq_PsiG Φ hVopen (fun z hz => hz.1) hS2 hPDE_v hSeq_v
      hsJetSeq_v hPsi hclair j
  have hder_u : ∀ j : ℕ, ∀ z ∈ V ∩ {z : ℝ × E | z.1 < T},
      AseqG Φ u j z = iteratedDeriv (j + 1) (fun s => u (s, z.2)) z.1 :=
    fun j => Work.Diff.EXT.gen.AseqG_eq_iteratedDeriv Φ hS1 hPDE_u j
  have hder_v : ∀ j : ℕ, ∀ z ∈ V ∩ {z : ℝ × E | T < z.1},
      AseqG Φ v j z = iteratedDeriv (j + 1) (fun s => v (s, z.2)) z.1 :=
    fun j => Work.Diff.EXT.gen.AseqG_eq_iteratedDeriv Φ hS2 hPDE_v j
  -- an open set on which the `t = T` slices agree
  obtain ⟨U, hUo, hy₀U, hUslice⟩ :=
    Work.Diff.EXT.gen.exists_open_slice_eq (T := T) (x₀ := y₀) hslice
  set U₁ : Set E := U ∩ Metric.ball y₀ ρ with hU₁def
  have hU₁o : IsOpen U₁ := hUo.inter Metric.isOpen_ball
  have hy₀U₁ : y₀ ∈ U₁ := ⟨hy₀U, by rw [Metric.mem_ball, dist_self]; exact hρ⟩
  have hxV : ∀ x ∈ U₁, (T, x) ∈ V := by
    intro x hx
    rw [hVdef, Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]; simp [hρ]
    · have := hx.2; rwa [Metric.mem_ball] at this
  -- the curves approaching the hyperplane from inside the two half-spaces
  have hcu : Tendsto (fun ε : ℝ => T - ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) := by
    have h1 : Tendsto (fun _ : ℝ => T) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h1.sub h2
  have hcv : Tendsto (fun ε : ℝ => T + ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) := by
    have h1 : Tendsto (fun _ : ℝ => T) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h1.add h2
  have hmemu : ∀ x ∈ U₁, ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      (T - ε, x) ∈ V ∩ {z : ℝ × E | z.1 < T} := by
    intro x hx
    have hxρ : dist x y₀ < ρ := by have := hx.2; rwa [Metric.mem_ball] at this
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < ρ from hρ))] with ε hε hερ
    have hε0 : 0 < ε := hε
    have hερ' : ε < ρ := hερ
    refine ⟨?_, ?_⟩
    · rw [hVdef, Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ hxρ
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    · exact sub_lt_self T hε0
  have hmemv : ∀ x ∈ U₁, ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      (T + ε, x) ∈ V ∩ {z : ℝ × E | T < z.1} := by
    intro x hx
    have hxρ : dist x y₀ < ρ := by have := hx.2; rwa [Metric.mem_ball] at this
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < ρ from hρ))] with ε hε hερ
    have hε0 : 0 < ε := hε
    have hερ' : ε < ρ := hερ
    refine ⟨?_, ?_⟩
    · rw [hVdef, Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ hxρ
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    · exact lt_add_of_pos_right T hε0
  -- the recursion at the hyperplane
  have hT_u : ∀ x ∈ U₁, ∀ j : ℕ,
      AseqG Φ u j (T, x) = PsiG Φ j (x, fun i : Fin (j + 1) => sJetG (SeqG Φ u i) (T, x)) :=
    fun x hx j => Work.Diff.EXT.gen.AseqG_eq_PsiG_at_of_curve Φ (fun j z hz => hrec_u j z hz)
      (fun j => ((hAseq_u j).continuousOn).continuousAt (hVopen.mem_nhds (hxV x hx)))
      (fun j => ((hPsiComp_u j).continuousOn).continuousAt (hVopen.mem_nhds (hxV x hx)))
      (fun ε => T - ε) hcu (hmemu x hx) j
  have hT_v : ∀ x ∈ U₁, ∀ j : ℕ,
      AseqG Φ v j (T, x) = PsiG Φ j (x, fun i : Fin (j + 1) => sJetG (SeqG Φ v i) (T, x)) :=
    fun x hx j => Work.Diff.EXT.gen.AseqG_eq_PsiG_at_of_curve Φ (fun j z hz => hrec_v j z hz)
      (fun j => ((hAseq_v j).continuousOn).continuousAt (hVopen.mem_nhds (hxV x hx)))
      (fun j => ((hPsiComp_v j).continuousOn).continuousAt (hVopen.mem_nhds (hxV x hx)))
      (fun ε => T + ε) hcv (hmemv x hx) j
  -- the iterated time derivatives at the hyperplane
  have hkey_u : ∀ x ∈ U₁, ∀ j : ℕ,
      iteratedDeriv (j + 1) (fun s : ℝ => u (s, x)) T = AseqG Φ u j (T, x) :=
    fun x hx j => Work.Diff.EXT.gen.iteratedDeriv_eq_AseqG_at_hyperplane Φ
      (huV.contDiffAt (hVopen.mem_nhds (hxV x hx)))
      (fun z hz => hder_u j z hz)
      (((hAseq_u j).continuousOn).continuousAt (hVopen.mem_nhds (hxV x hx)))
      (fun ε => T - ε) hcu (hmemu x hx)
  have hkey_v : ∀ x ∈ U₁, ∀ j : ℕ,
      iteratedDeriv (j + 1) (fun s : ℝ => v (s, x)) T = AseqG Φ v j (T, x) :=
    fun x hx j => Work.Diff.EXT.gen.iteratedDeriv_eq_AseqG_at_hyperplane Φ
      (hvV.contDiffAt (hVopen.mem_nhds (hxV x hx)))
      (fun z hz => hder_v j z hz)
      (((hAseq_v j).continuousOn).continuousAt (hVopen.mem_nhds (hxV x hx)))
      (fun ε => T + ε) hcv (hmemv x hx)
  -- the time Taylor coefficients of `u` and `v` agree on `U₁`
  have hgamma : ∀ x ∈ U₁, ∀ i : ℕ,
      iteratedDeriv i (fun s : ℝ => u (s, x)) T = iteratedDeriv i (fun s : ℝ => v (s, x)) T :=
    Work.Diff.EXT.gen.time_derivs_agree_at_hyperplane Φ hU₁o (fun x hx => hUslice x hx.1)
      hT_u hT_v hkey_u hkey_v
  -- hence the time Taylor coefficients of `u - v` vanish along the hyperplane over `U₁`
  have hflat : ∀ x ∈ U₁, ∀ i : ℕ,
      iteratedDeriv i (fun s : ℝ => (u - v) (s, x)) T = 0 := by
    intro x hx i
    have hfu : ContDiffAt ℝ (↑i) (fun s : ℝ => u (s, x)) T :=
      (ContDiffAt.comp T (huV.contDiffAt (hVopen.mem_nhds (hxV x hx)))
        (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
    have hfv : ContDiffAt ℝ (↑i) (fun s : ℝ => v (s, x)) T :=
      (ContDiffAt.comp T (hvV.contDiffAt (hVopen.mem_nhds (hxV x hx)))
        (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
    have h1 : iteratedDeriv i (fun s : ℝ => (u - v) (s, x)) T
        = iteratedDeriv i (fun s : ℝ => u (s, x)) T
          - iteratedDeriv i (fun s : ℝ => v (s, x)) T :=
      iteratedDeriv_sub hfu hfv
    rw [h1, hgamma x hx i, sub_self]
  -- the difference is flat, hence the Heaviside cut is smooth
  have hstep : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => if p.1 ≤ T then (0 : MatE (E := E)) else u p - v p) (T, y₀) :=
    Work.Diff.EXT.gen.flat_indicator_E (F := MatE (E := E)) hVopen hTV (huV.sub hvV)
      hU₁o hy₀U₁ hflat
  have hEq : (fun p : ℝ × E => if p.1 ≤ T then u p else v p)
      = fun p => u p - (if p.1 ≤ T then (0 : MatE (E := E)) else u p - v p) := by
    funext p
    by_cases hp : p.1 ≤ T <;> simp [hp]
  rw [hEq]
  exact (hu.contDiffAt (hB.mem_nhds hB₀)).sub hstep

end Work.Diff.EXT
