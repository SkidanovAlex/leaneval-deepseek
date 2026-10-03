import Mathlib
import Submission.Work.Repel.V10.chain_v9_src

/-!
# `Work.Repel.Raw_open` : the raw source region of a §6 cell is open

The raw source region of a cell `(j, k)` is

  `Raw j k = {w : ℂ | s · π w ∈ φ₁ '' (W j + k)}`

(`chain_v9_src`).  It is the `(s·π)`-preimage of the image of the *chain fibre*
`fib j k = W j + k` under the level-1 Fatou coordinate `φ₁ = V.P₁.φ`, so it suffices that this
image be open.

For that, note that `fib j k` is open and connected (a translate of `W j`, which `IsChain` gives
open and connected), that `φ₁` is holomorphic on a neighbourhood of it (`fib j k ⊆ Sm1 ⊆ Dφ`), and
that `φ₁` is *not* constant on it: `Sm1_injOn` makes `φ₁` injective on `Sm1 ⊇ fib j k`, while an
open nonempty subset of `ℂ` has at least two points.  The open mapping theorem
(`AnalyticOnNhd.is_constant_or_isOpen`) then gives that `φ₁` sends every open subset of `fib j k`
— in particular the fibre itself — to an open set, and the result follows from continuity of
`w ↦ s · π w`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

theorem Raw_open (V : Work.Repel.V10) {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) :
    IsOpen (V.Raw j k) := by
  -- the fibre is a translate of the open connected set `W j`
  have hfibopen : IsOpen (V.fib j k) :=
    (Homeomorph.isOpen_image (Homeomorph.addRight ((k : ℤ) : ℂ))).mpr
      (V.hIsChain.open_conn j).1
  have hfibconn : IsConnected (V.fib j k) :=
    (Homeomorph.isConnected_image (Homeomorph.addRight ((k : ℤ) : ℂ))).mpr
      (V.hIsChain.open_conn j).2
  -- `φ₁` is holomorphic (indeed analytic) on the fibre
  have hsub : V.fib j k ⊆ V.P₁.Dφ := fun u hu => V.Sm1_sub_Dφ (hSm hu)
  have hanal : AnalyticOnNhd ℂ V.P₁.φ (V.fib j k) :=
    (V.P₁.φ_holo.mono hsub).analyticOnNhd hfibopen
  -- `w ↦ s · π w` is continuous
  have hcont : Continuous fun w : ℂ => V.s * MandelDim.piExp w :=
    Continuous.const_mul (Complex.continuous_exp.comp (by fun_prop)) V.s
  have hset : V.Raw j k
      = (fun w : ℂ => V.s * MandelDim.piExp w) ⁻¹' (V.P₁.φ '' V.fib j k) := rfl
  rcases hanal.is_constant_or_isOpen hfibconn.isPreconnected with hconst | hopen
  · -- `φ₁` is injective on `Sm1 ⊇ fib j k` and the fibre has two distinct points
    exfalso
    obtain ⟨c, hc⟩ := hconst
    obtain ⟨w, hw⟩ : (V.fib j k).Nonempty := ⟨V.uc j + ((k : ℤ) : ℂ), V.uc_fib j k⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hfibopen.mem_nhds hw)
    have hε2 : ((ε / 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hε))
    have hmem : w + ((ε / 2 : ℝ) : ℂ) ∈ V.fib j k := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : (w + ((ε / 2 : ℝ) : ℂ)) - w = ((ε / 2 : ℝ) : ℂ) := by ring
      rw [h1]
      have h2 : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
        rw [show ‖((ε / 2 : ℝ) : ℂ)‖ = |ε / 2| by exact RCLike.norm_ofReal (ε / 2)]
        exact abs_of_pos (half_pos hε)
      rw [h2]
      linarith
    have hne : w + ((ε / 2 : ℝ) : ℂ) ≠ w := by
      intro h
      have hc0 : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have := congrArg (fun z : ℂ => z - w) h
        simpa using this
      exact hε2 hc0
    exact hne (V.Sm1_injOn (hSm hw) (hSm hmem) ((hc w hw).trans (hc _ hmem).symm)).symm
  · -- openness of the image, then pull back along the continuous map `s · π`
    rw [hset]
    exact ((hopen _ Subset.rfl hfibopen).preimage hcont)

end

end Work.Repel
