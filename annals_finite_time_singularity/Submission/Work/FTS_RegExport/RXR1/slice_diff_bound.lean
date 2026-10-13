import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_EllLimOK.LimTower_dz
import Submission.Work.FTS_EllLimOK.LimTower_identify
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS_EllLimOK.abs_sub_le_of_box_bounds
import Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0
import Submission.Work.FTS_EllLimOK.LimExtract_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.slice_diff_bound`

The `τ`-Lipschitz modulus of the order-`≤ 2` mixed jets of the slices of the strong solution
`g` of the fake-time equation (the "difference" half of the consistency statement RX-A2):

`|D_z^b D_θ^a (g(·,·,τ) - g(·,·,τ'))(z,θ)| ≤ 10/√(γ-1) · L · |τ - τ'|`

for `a + b ≤ 2` and `(z,θ)` in the open quadrant, with `L` the `ℋ⁴`-Lipschitz modulus of the
class-C approximants supplied by `LimApprox`.

## The route

`LimApprox α C₀ Φs E g` provides a sequence `gn` of class-C families, uniformly in `ℋ⁶`, whose
`ℋ⁴`-differences are `L`-Lipschitz in `τ`, and whose mixed jets converge pointwise on the open
quadrant (`Qd = Q0`) to those of `g`.

1. For fixed `τ, τ'` the *difference* family `H n = slice (gn n) τ - slice (gn n) τ'` is
   `C^∞` on the open quadrant (`EComparison.classC_sub`), and `ZsqAux.mixed_sub_open` rewrites
   its jets as differences of the jets of the two class-C slices.  The class-C bound
   `classC_mixed_sup_le_four` (order `≤ 4`) then bounds the order-`≤ 3` jets of `H n`
   *uniformly in `n`, `z`, `θ`*; the identities `∂_z (mixed c d) = mixed (c+1) d / z`,
   `∂_θ (mixed c d) = mixed c (d+1) / sin 2θ` (`mixed_partials_of_smoothOpen`) make the
   order-`≤ 2` jets uniformly Lipschitz on every compact subset of the open quadrant, and
   `eqc_uniform` converts pointwise convergence + equicontinuity into
   `TendstoLocallyUniformlyOn`.
2. `LimTower_dz` turns the locally uniform convergence into the two tower relations
   `∂_z (F c d) = F (c+1) d / z`, `∂_θ (F c d) = F c (d+1) / sin 2θ` for the limit family
   `F c d := mixed c d (slice g τ) - mixed c d (slice g τ')`; `LimTower_identify` then
   identifies `F c d` with `mixed c d (F 0 0) = D_z^c D_θ^d (slice g τ - slice g τ')`.
3. The pointwise class-C bound `|mixed b a (H n) z θ| ≤ 10/√(γ-1) · ℋ⁴(H n)` (RX-A1 on the
   open class, `mixed_abs_le_of_smoothOpen`) together with the Lipschitz clause of `LimApprox`
   bounds `|F b a z θ|`; the bound passes to the limit (`le_of_tendsto'`).
-/

namespace Work.FTS_RegExport.RXR1

open Filter Set
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## §1 Uniform convergence on compacta from pointwise convergence and equicontinuity -/

/-- Pointwise convergence of a sequence of real-valued functions plus uniform equicontinuity on
a compact set gives uniform convergence there (the scalar version of
`Work.FTS.StrongEps.LocUnif.tendstoUniformlyOn_of_pointwise_of_equicont`). -/
theorem eqc_uniform {K : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    (hK : IsCompact K)
    (hpt : ∀ p ∈ K, Filter.Tendsto (fun n => F n p) Filter.atTop (nhds (f p)))
    (heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → dist (F n p) (F n q) < ε) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨δ, hδpos, hδ⟩ := heqc (ε / 3) hε3
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun p => Metric.ball p δ)
    (fun p _ => Metric.ball_mem_nhds p hδpos)
  have hcen : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, dist (F n y) (f y) < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y hy
    exact (hpt y (htK y hy)).eventually (Metric.ball_mem_nhds (f y) hε3)
  filter_upwards [hcen] with n hn
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have hxyδ : dist x y < δ := by simpa [Metric.mem_ball] using hxy
  have hny' : dist (f y) (F n y) < ε / 3 := by
    have h0 := hn y hyt
    rwa [dist_comm] at h0
  have hFnyx : dist (F n y) (F n x) < ε / 3 := by
    have h1 : dist (F n x) (F n y) < ε / 3 := hδ n x hx y (htK y hyt) hxyδ
    rwa [dist_comm] at h1
  have hfyx : dist (f x) (f y) ≤ ε / 3 := by
    refine le_of_tendsto' ((hpt x hx).dist (hpt y (htK y hyt))) (fun m => ?_)
    exact le_of_lt (hδ m x hx y (htK y hyt) hxyδ)
  have htri : dist (f x) (F n x) ≤
      dist (f x) (f y) + dist (f y) (F n y) + dist (F n y) (F n x) :=
    dist_triangle4 _ _ _ _
  linarith

/-! ## §2 Locally uniform convergence of the jets of the approximant differences -/

/-- The mixed jets of `slice (gn n) τ - slice (gn n) τ'` converge *locally uniformly* on the
open quadrant to the difference of the mixed jets of the limiting slices, when the class-C
families `gn n` are uniformly bounded in `ℋ⁶` and their jets converge pointwise to those of
`g` (the hypotheses extracted from `LimApprox`). -/
theorem jetLocUnif_fb {α T B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g : Work.FTS.Galerkin.Fam} {gn : ℕ → Work.FTS.Galerkin.Fam}
    (hC : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (gn n) τ))
    (hB : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (gn n) τ) ≤ B)
    (hJet : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)))
    {τ τ' : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) (hτ' : τ' ∈ Set.Icc (0:ℝ) T)
    (c d : ℕ) (hcd : c + d ≤ 2) :
    TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.Spaces.mixed c d
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') p.1 p.2)
      (fun (p : ℝ × ℝ) => Work.Spaces.mixed c d (Work.FTS.Galerkin.slice g τ) p.1 p.2
        - Work.Spaces.mixed c d (Work.FTS.Galerkin.slice g τ') p.1 p.2)
      Filter.atTop Work.FTS.EllipticEst.Q0 := by
  have hpi := Real.pi_pos
  -- the difference family is `C^∞` on the open quadrant
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') := fun n =>
    (Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ) (hC n τ' hτ')).reg
  -- pointwise convergence of the difference jets
  have hpt : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') p.1 p.2)
        Filter.atTop (nhds (Work.Spaces.mixed c d (Work.FTS.Galerkin.slice g τ) p.1 p.2
          - Work.Spaces.mixed c d (Work.FTS.Galerkin.slice g τ') p.1 p.2)) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hsum := (hJet τ hτ c d (by omega) p.1 p.2 ⟨hz, hθ0, hθ1⟩).sub
      (hJet τ' hτ' c d (by omega) p.1 p.2 ⟨hz, hθ0, hθ1⟩)
    refine hsum.congr' ?_
    filter_upwards with n
    exact (Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).reg (hC n τ' hτ').reg
      c d p.1 p.2 hz hθ0 hθ1).symm
  -- the uniform bound on the order-`≤ 3` jets of the difference family
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  have hKc0 : 0 ≤ C4 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg hC4pos.le (Real.sqrt_nonneg _)
  set M : ℝ := 2 * (C4 / Real.sqrt (Work.Spaces.gam α - 1) * max B 0) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (by norm_num) (mul_nonneg hKc0 (le_max_right B 0))
  have hbnd : ∀ (n j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ| ≤ M := by
    intro n j i hji z θ hQ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    have hsplit : Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ
        = Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ') z θ :=
      Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).reg (hC n τ' hτ').reg
        j i z θ hz hθ0 hθ1
    have b1 := hC4 α ⟨hα, hα1⟩ (hC n τ hτ) j i (by omega) (z := z) (θ := θ) hQ
    have b2 := hC4 α ⟨hα, hα1⟩ (hC n τ' hτ') j i (by omega) (z := z) (θ := θ) hQ
    have e1 : C4 / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ C4 / Real.sqrt (Work.Spaces.gam α - 1) * max B 0 :=
      mul_le_mul_of_nonneg_left (le_trans (hB n τ hτ) (le_max_left B 0)) hKc0
    have e2 : C4 / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (gn n) τ')
        ≤ C4 / Real.sqrt (Work.Spaces.gam α - 1) * max B 0 :=
      mul_le_mul_of_nonneg_left (le_trans (hB n τ' hτ') (le_max_left B 0)) hKc0
    calc |Work.Spaces.mixed j i
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ|
        = |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ') z θ| := by rw [hsplit]
      _ ≤ |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
            + |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ') z θ| := by
          have hh := abs_sub_le
            (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ) 0
            (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ') z θ)
          simpa using hh
      _ ≤ C4 / Real.sqrt (Work.Spaces.gam α - 1) * max B 0
            + C4 / Real.sqrt (Work.Spaces.gam α - 1) * max B 0 :=
          add_le_add (le_trans b1 e1) (le_trans b2 e2)
      _ = M := by rw [hMdef]; ring
  -- locally uniform convergence
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
  intro K hKQ hKc
  refine eqc_uniform hKc (fun p hp => hpt p (hKQ hp)) ?_
  intro ε hε
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun n p hp => absurd hp (Set.notMem_empty p)⟩
  obtain ⟨a, b, c₀, d₀, ha, hab, hc₀, hc₀d₀, hd₀, hbox⟩ :=
    Work.FTS_EllLimOK.box_of_compact_inside_Q0 hKc hKQ hne
  -- the angular lower bound on the box
  set S : ℝ := 2 * Real.sin c₀ * Real.cos d₀ with hSdef
  have hSpos : 0 < S := by
    rw [hSdef]
    exact mul_pos (mul_pos (by norm_num)
        (Real.sin_pos_of_pos_of_lt_pi hc₀ (by linarith)))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  have hSle : ∀ θ ∈ Set.Icc c₀ d₀, S ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le hc₀ hθ.1
    have hθlt : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hd₀
    have hsinmono : MonotoneOn Real.sin (Set.Icc 0 (Real.pi / 2)) :=
      Real.strictMonoOn_sin.monotoneOn.mono (by
        intro x hx
        exact ⟨by linarith [hpi, hx.1], hx.2⟩)
    have hcosanti : AntitoneOn Real.cos (Set.Icc 0 (Real.pi / 2)) :=
      Real.strictAntiOn_cos.antitoneOn.mono (by
        intro x hx
        exact ⟨hx.1, by linarith [hpi, hx.2]⟩)
    have hs1 : Real.sin c₀ ≤ Real.sin θ :=
      hsinmono ⟨hc₀.le, by linarith [hpi, hc₀d₀, hd₀]⟩ ⟨hθpos.le, by linarith [hpi, hθlt]⟩ hθ.1
    have hs2 : Real.cos d₀ ≤ Real.cos θ :=
      hcosanti ⟨hθpos.le, by linarith [hpi, hθlt]⟩
        ⟨le_trans hc₀.le hc₀d₀, le_of_lt hd₀⟩ hθ.2
    have hs3 : 0 ≤ Real.sin c₀ :=
      (Real.sin_pos_of_pos_of_lt_pi hc₀ (by linarith)).le
    have hc4 : 0 ≤ Real.cos d₀ :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
    have hstep : Real.sin c₀ * Real.cos d₀ ≤ Real.sin θ * Real.cos θ :=
      mul_le_mul hs1 hs2 hc4 (le_trans hs3 hs1)
    calc S = 2 * Real.sin c₀ * Real.cos d₀ := hSdef
      _ ≤ 2 * Real.sin θ * Real.cos θ := by linarith [hstep]
      _ = Real.sin (2 * θ) := (Real.sin_two_mul θ).symm
  -- the box is inside the open quadrant
  have hboxQ : ∀ z θ : ℝ, (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c₀ d₀ →
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hzθ.1.1, lt_of_lt_of_le hc₀ hzθ.2.1, lt_of_le_of_lt hzθ.2.2 hd₀⟩
  -- the common Lipschitz constant on the box
  set L : ℝ := M / a + M / S with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact add_nonneg (div_nonneg hM0 ha.le) (div_nonneg hM0 hSpos.le)
  have hpzb : ∀ n : ℕ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      |Work.Spaces.pz (Work.Spaces.mixed c d
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')) z θ| ≤ L := by
    intro n z hz θ hθ
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ z θ (Set.mem_prod.mpr ⟨hz, hθ⟩)
    obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d (hsm n)).1 z θ hQ,
      abs_div, abs_of_pos hzpos]
    have hnum := hbnd n (c + 1) d (by omega) z θ hQ
    calc |Work.Spaces.mixed (c + 1) d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ| / z
        = |Work.Spaces.mixed (c + 1) d
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ|
            * (1 / z) := by ring
      _ ≤ M * (1 / z) := mul_le_mul_of_nonneg_right hnum (le_of_lt (one_div_pos.mpr hzpos))
      _ ≤ M * (1 / a) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha hz.1) hM0
      _ = M / a := by ring
      _ ≤ L := by rw [hLdef]; exact le_add_of_nonneg_right (div_nonneg hM0 hSpos.le)
  have hpthb : ∀ n : ℕ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      |Work.Spaces.pth (Work.Spaces.mixed c d
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')) z θ| ≤ L := by
    intro n z hz θ hθ
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ z θ (Set.mem_prod.mpr ⟨hz, hθ⟩)
    obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d (hsm n)).2.1 z θ hQ,
      abs_div, abs_of_pos hsinpos]
    have hnum := hbnd n c (d + 1) (by omega) z θ hQ
    calc |Work.Spaces.mixed c (d + 1)
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ|
          / Real.sin (2 * θ)
        = |Work.Spaces.mixed c (d + 1)
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ|
            * (1 / Real.sin (2 * θ)) := by ring
      _ ≤ M * (1 / Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_right hnum (le_of_lt (one_div_pos.mpr hsinpos))
      _ ≤ M * (1 / S) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hSpos (hSle θ hθ)) hM0
      _ = M / S := by ring
      _ ≤ L := by rw [hLdef]; exact le_add_of_nonneg_left (div_nonneg hM0 ha.le)
  refine ⟨ε / (2 * L + 1), div_pos hε (by linarith), ?_⟩
  intro n p hp q hq hpq
  have hpbox : p ∈ Set.Icc a b ×ˢ Set.Icc c₀ d₀ := hbox hp
  have hqbox : q ∈ Set.Icc a b ×ˢ Set.Icc c₀ d₀ := hbox hq
  have hzw : ∀ θ ∈ Set.Icc c₀ d₀, ∀ z ∈ Set.Icc a b,
      HasDerivWithinAt (fun z' : ℝ => Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z' θ)
        (Work.Spaces.pz (Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')) z θ)
        (Set.Icc a b) z := by
    intro θ hθ z hz
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ z θ (Set.mem_prod.mpr ⟨hz, hθ⟩)
    obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    exact (((hsm n).mixed c d).hasDerivAt_slice ⟨hθ0, hθ1⟩ hzpos).hasDerivWithinAt
  have hthw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      HasDerivWithinAt (fun θ' : ℝ => Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ')
        (Work.Spaces.pth (Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')) z θ)
        (Set.Icc c₀ d₀) θ := by
    intro z hz θ hθ
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ z θ (Set.mem_prod.mpr ⟨hz, hθ⟩)
    obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    exact (Work.FTS_EllLimOK.smoothOpen_hasDerivAt_slice_theta ((hsm n).mixed c d) hzpos
      ⟨hθ0, hθ1⟩).hasDerivWithinAt
  have hboxb := Work.FTS_EllLimOK.abs_sub_le_of_box_bounds
    (g := fun z θ => Work.Spaces.mixed c d
      (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ)
    (a := a) (b := b) (c := c₀) (d := d₀) (L := L) hzw hthw (hpzb n) (hpthb n) p hpbox q hqbox
  have hdist1 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hdist2 : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  rw [Real.dist_eq]
  calc |Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') p.1 p.2
        - Work.Spaces.mixed c d
          (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') q.1 q.2|
      ≤ L * (|p.1 - q.1| + |p.2 - q.2|) := hboxb
    _ ≤ L * (2 * dist p q) := by
        refine mul_le_mul_of_nonneg_left ?_ hL0
        linarith
    _ = 2 * L * dist p q := by ring
    _ ≤ 2 * L * (ε / (2 * L + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hpq) (by linarith)
    _ = 2 * L * ε / (2 * L + 1) := by ring
    _ < ε := by
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * L + 1)]
        nlinarith [hε, hL0]

/-! ## §3 The Lipschitz modulus of the slice differences -/

theorem slice_diff_bound {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          10 / Real.sqrt (Work.Spaces.gam α - 1) * L * |τ - τ'| := by
  obtain ⟨gn, B, L₀, hClass, hLip, hJet, -⟩ := hA T hT
  refine ⟨max L₀ 0, le_max_right L₀ 0, ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  -- the limit family on `Q0`
  set F : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d z θ =>
    Work.Spaces.mixed c d (Work.FTS.Galerkin.slice g τ) z θ
      - Work.Spaces.mixed c d (Work.FTS.Galerkin.slice g τ') z θ with hFdef
  -- locally uniform convergence of the jets of the approximant differences
  have hLU : ∀ c d : ℕ, c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.Spaces.mixed c d
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') p.1 p.2)
      (fun (p : ℝ × ℝ) => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    have h := jetLocUnif_fb hα hα1 (g := g) (gn := gn) (T := T) (B := B)
      (fun n τ'' hτ'' => (hClass n τ'' hτ'').1)
      (fun n τ'' hτ'' => (hClass n τ'' hτ'').2.2)
      hJet hτ hτ' c d hcd
    simpa only [hFdef] using h
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') := fun n =>
    (Work.FTS.StrongEps.EComparison.classC_sub (hClass n τ hτ).1 (hClass n τ' hτ').1).reg
  -- the two tower relations, and the identification of `F` with the jets of the difference
  obtain ⟨hdz, hdth⟩ := Work.FTS_EllLimOK.LimTower_dz
    (G := fun n => Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')
    (φ := id) (F := F) hsm hLU
  have hident := Work.FTS_EllLimOK.LimTower_identify (F := F) hdz hdth
  have hF00 : F 0 0 = (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') := by
    funext z' θ'
    simp only [hFdef, Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero]
    rfl
  have hkey : F b a z θ
      = Work.Spaces.mixed b a
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ := by
    have h1 := hident b a (by omega) z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
    rwa [hF00] at h1
  -- the pointwise convergence at `(z,θ)`
  have hpt : Filter.Tendsto (fun n => Work.Spaces.mixed b a
      (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ)
      Filter.atTop (𝓝 (F b a z θ)) :=
    (hLU b a (by omega)).tendsto_at
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
  -- the per-`n` bound
  have hbnd : ∀ n : ℕ, |Work.Spaces.mixed b a
      (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| := by
    intro n
    have hsub := Work.FTS.StrongEps.EComparison.classC_sub (hClass n τ hτ).1
      (hClass n τ' hτ').1
    have h1 := Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen (α := α) hα hα1
      hsub.reg (Work.FTS.ClassC.classC_hkMem_four hsub) (hsub.bdry_le_six (by norm_num))
      b a hab hz hθ0 hθ1
    have h2 : Work.Spaces.HkNorm α 4
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ')
        ≤ L₀ * |τ - τ'| := hLip n τ hτ τ' hτ'
    have h3 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have h4 : L₀ * |τ - τ'| ≤ max L₀ 0 * |τ - τ'| :=
      mul_le_mul_of_nonneg_right (le_max_left L₀ 0) (abs_nonneg _)
    calc |Work.Spaces.mixed b a
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4
            (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) τ') := h1
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L₀ 0 * |τ - τ'|) :=
          mul_le_mul_of_nonneg_left (le_trans h2 h4) h3
      _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| := by ring
  have hlim : |F b a z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| :=
    le_of_tendsto' hpt.abs hbnd
  rwa [← hkey]

end

end Work.FTS_RegExport.RXR1
