import Mathlib
import Submission.Work.LayerCont.LowBadClosureEight

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- **The closure transfer for BOTH dimensions, with cleanliness as the hypothesis.**

`Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` bounds `Kaxis (Kfun ℓ d)` on `lowBadSet` for
`d = 8` and `d = 24` alike, with the guard `1/8 ≤ |t - τ.im|`.  This transfers that bound to the
*closure* of `lowBadSet` — the part the continuation needs, since `closure lowBadSet` meets the bad
lines `Re τ = ±1` — **assuming the contour is clean at the point in question**
(`jInvariantFun τ ≠ jInvariantFun (imagAxis t ht)`).

That hypothesis is not a weakening for the intended application: the differentiation-under-the-
integral-sign argument for `TruncHolomorphy` runs with exactly this cleanliness on the retained set
`E = Ici 1 \ Ioo (t₀-A) (t₀+A)`, and it is what makes the transfer *dimension-free*.  Without it the
`d = 24` S-branch coincidence `j τ = j (i t)` would have to be handled separately, because there
Lean's `Kaxis` is a finite definitional object that differs from the mathematical (removable) value
— see `Submission/ROADMAP.md`, entry `The transfer, sharpened`; the `d = 8` case needs no such care
(`Work.LayerCont.LowBadClosureEight`, where the value is `0`).

The proof is the limit argument: at a clean point `τ ↦ Kaxis (Kfun ℓ d) τ t` is continuous
(`Work.Asymptotics.differentiableAt_Kfun_tau` at `(τ, imagAxis t ht)`, lifted to `ℍ` by
`UpperHalfPlane.mdifferentiableAt_iff`), the aux bound holds `∀ᶠ` on `𝓝[lowBadSet] τ`, and
`le_of_tendsto` passes it to the limit.  The guard must be **strict**: `{τ | 1/8 < |t - τ.im|}` is
open (`isOpen_lt`), hence a neighbourhood of `τ`, which is what makes the aux bound available
eventually.

(We do not even need `hclean` at the varying `τ ∈ lowBadSet`, only at the limit point.) -/
theorem LowBadClosureClean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsub : K ⊆ closure Work.Asymptotics.HalfFunnel.lowBadSet)
    (hclean : ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t), t ≤ Work.Asymptotics.HalfFunnel.lowT →
      (1 / 8 : ℝ) < |t - τ.im| →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT → (1 / 8 : ℝ) < |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux ℓ d hd
  refine ⟨C, hC, fun τ₀ t hτK ht htT hsep => ?_⟩
  have hτ₀ : τ₀ ∈ closure Work.Asymptotics.HalfFunnel.lowBadSet := hsub hτK
  have hJ := hclean τ₀ hτK t ht htT hsep
  have hdiff : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) τ₀ := by
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    have hfun : ((fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
          ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane))
        = fun w : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex w)
            (Work.Kernels.imagAxis t ht) := by
      funext w
      simp only [Function.comp_apply]
      rw [Work.Kernels.Kaxis, dif_pos ht]
    rw [hfun]
    exact Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
      (τ := τ₀) (z := Work.Kernels.imagAxis t ht) hJ
  have hct : ContinuousAt
      (fun τ : UpperHalfPlane => ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖) τ₀ :=
    (continuous_norm.continuousAt).comp hdiff.continuousAt
  have htend : Tendsto (fun τ : UpperHalfPlane =>
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖)
      (𝓝[Work.Asymptotics.HalfFunnel.lowBadSet] τ₀)
      (𝓝 ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ₀ t‖) :=
    hct.tendsto.mono_left nhdsWithin_le_nhds
  have himcont : Continuous (fun τ : UpperHalfPlane => |t - τ.im|) := by fun_prop
  have hopen : IsOpen {τ : UpperHalfPlane | (1 / 8 : ℝ) < |t - τ.im|} :=
    isOpen_lt continuous_const himcont
  have hev : ∀ᶠ τ in 𝓝 τ₀, (1 / 8 : ℝ) < |t - τ.im| := hopen.mem_nhds hsep
  haveI : NeBot (𝓝[Work.Asymptotics.HalfFunnel.lowBadSet] τ₀) :=
    mem_closure_iff_nhdsWithin_neBot.mp hτ₀
  have hfreq : ∀ᶠ τ in 𝓝[Work.Asymptotics.HalfFunnel.lowBadSet] τ₀,
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with τ hsep' hτ
    exact hb τ t hτ ht htT hsep'.le
  exact le_of_tendsto htend hfreq

end Work.LayerCont
