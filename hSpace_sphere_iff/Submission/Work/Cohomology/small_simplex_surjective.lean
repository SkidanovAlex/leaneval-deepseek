import Mathlib
import Submission.Work.Cohomology.SingIn
import Submission.Work.Cohomology.chainMap_singIn
import Submission.Work.Cohomology.chainMap_sup
import Submission.Work.Cover.exists_small_cycle_homologous
import Submission.Work.Cover.exists_small_boundary
import Submission.Work.Cohomology.Pairing
import Submission.Work.Pairing.pairMap_range
import Submission.Work.Pairing.pairMap_injective

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Cohomology

/-- **The small-simplex theorem, surjectivity half.**  Let `X` be a topological space with an open
cover `X = U ∪ V` and let `small := singIn X U ⊔ singIn X V`.  Then the restriction map
`H (Sing X) ℚ k → H small ℚ k` is surjective: every cohomology class on the small complex is the
restriction of a class on `X`.

Proof plan (via the evaluation pairing `pairMap` of `Work.Pairing`, whose range is the annihilator
of the boundaries of the cycles).  Given `z : H small ℚ k`, put `φ := pairMap small k z`.  Define a
functional `ψ` on the cycles of `Sing X` by `ψ c := φ c''`, where `c'` is a cycle of `Sing X` with
`c' ∈ chainIn X U k ⊔ chainIn X V k` and `c' - c` a boundary (exists by
`Work.Cover.exists_small_cycle_homologous`) and `c''` is the unique chain of `small` with
`chainMap ℚ small.ι k c'' = c'` (using `Work.Cohomology.chainMap_sup`,
`Work.Cohomology.chainMap_singIn`).  Well-definedness and linearity use that `φ` annihilates the
boundaries of `small` (`pairMap` lands in the annihilator) together with
`Work.Cover.exists_small_boundary`: a small cycle which is a boundary of `Sing X` is a boundary of
`small`.  Then `ψ` annihilates the boundaries of `Sing X` (if `c = sbdry d` then a corresponding
small `c'` is a boundary of `Sing X`, hence by `exists_small_boundary` a boundary of `small`, so
`φ c'' = 0`).  By `Work.Pairing.pairMap_range` and
`Work.Pairing.pairMap_injective` there is `x : H (Sing X) ℚ k` with `pairMap (Sing X) k x = ψ`, and
`pairMap_natural` gives `pairMap small k (H.map ℚ small.ι k x) = ψ ∘ cycleChainMap small.ι k`;
evaluating both sides on a small cycle shows that this equals `pairMap small k z`, so
`H.map ℚ small.ι k x = z` by `pairMap_injective`. -/
theorem small_simplex_surjective (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x, x ∈ U ∨ x ∈ V) (k : ℕ) :
    Function.Surjective (Submission.Cohomology.H.map ℚ
      (Submission.Cohomology.singIn X U ⊔ Submission.Cohomology.singIn X V).ι k) := by
  set small : (TopCat.toSSet.obj X).Subcomplex := singIn X U ⊔ singIn X V with hsmall
  intro z
  -- The range and injectivity of the chain map of the inclusion `small ⟶ Sing X`.
  have range_small : ∀ n, (chainMap ℚ small.ι n).range = chainIn X U n ⊔ chainIn X V n := by
    intro n; rw [hsmall]
    rw [(chainMap_sup (TopCat.toSSet.obj X) (singIn X U) (singIn X V) n).1,
      (chainMap_singIn X U n).1, (chainMap_singIn X V n).1]
  have inj_small : ∀ n, Function.Injective (chainMap ℚ small.ι n) := by
    intro n; rw [hsmall]
    exact (chainMap_sup (TopCat.toSSet.obj X) (singIn X U) (singIn X V) n).2
  -- Key point: a small cycle whose image in `Sing X` is a boundary already pairs to zero with `z`.
  have hk : LinearMap.ker ((Submodule.mkQ (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k)).comp
        (cycleChainMap small.ι k)) ≤ LinearMap.ker (pairMap small k z) := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hb : chainMap ℚ small.ι k w.1 ∈ chainBoundaries (TopCat.toSSet.obj X) ℚ k := by
      have h := hw
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      exact h
    have hsm : chainMap ℚ small.ι k w.1 ∈ chainIn X U k ⊔ chainIn X V k := by
      rw [← range_small]; exact LinearMap.mem_range_self _ _
    obtain ⟨d, hdmem, hd⟩ := Work.Cover.exists_small_boundary X U V hU hV hUV k _ hsm hb
    obtain ⟨d'', hd''⟩ : d ∈ (chainMap ℚ small.ι (k+1)).range := by
      rw [range_small]; exact hdmem
    have hsb : sbdry small ℚ k d'' = w.1 := by
      apply inj_small
      rw [chainMap_sbdry, hd'', hd]
    have hwB : w.1 ∈ chainBoundaries small ℚ k := ⟨d'', hsb⟩
    have hwBic : w ∈ chainBoundariesInCycles small ℚ k := by
      rw [chainBoundariesInCycles, Submodule.mem_comap]; exact hwB
    have hann : pairMap small k z ∈ (chainBoundariesInCycles small ℚ k).dualAnnihilator := by
      rw [← Work.Pairing.pairMap_range]; exact LinearMap.mem_range_self _ _
    exact (Submodule.mem_dualAnnihilator _).mp hann w hwBic
  -- `φ := pairMap small k z` kills the boundaries of `small` along the composite
  -- `small-cycles → Sing X-cycles → Sing X-cycles/boundaries`.
  have hφ : pairMap small k z ∈ (LinearMap.ker ((Submodule.mkQ
        (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k)).comp
        (cycleChainMap small.ι k))).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact LinearMap.mem_ker.mp (hk hw)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker ((Submodule.mkQ
      (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k)).comp (cycleChainMap small.ι k))] at hφ
  obtain ⟨ψbar, hψbar⟩ := hφ
  -- `ψ` is the functional on the cycles of `Sing X` which kills the boundaries and whose
  -- restriction to the small cycles is `pairMap small k z`.
  let ψ : chainCycles (TopCat.toSSet.obj X) ℚ k →ₗ[ℚ] ℚ :=
    ψbar.comp (Submodule.mkQ (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k))
  have hψB : chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k ≤ LinearMap.ker ψ := by
    intro b hb
    rw [LinearMap.mem_ker]
    have hb0 : (Submodule.mkQ (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k)) b = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hb
    change ψbar ((Submodule.mkQ (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k)) b) = 0
    rw [hb0, map_zero]
  have hψann : ψ ∈ (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro b hb
    exact LinearMap.mem_ker.mp (hψB hb)
  have hmem : ψ ∈ (pairMap (TopCat.toSSet.obj X) k).range := by
    rw [Work.Pairing.pairMap_range]; exact hψann
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  apply Work.Pairing.pairMap_injective small k
  rw [pairMap_natural small.ι k x, hx]
  ext w
  change ψ (cycleChainMap small.ι k w) = pairMap small k z w
  have h1 : ψ (cycleChainMap small.ι k w)
      = (((Submodule.mkQ (chainBoundariesInCycles (TopCat.toSSet.obj X) ℚ k)).comp
          (cycleChainMap small.ι k)).dualMap ψbar) w := by
    rw [LinearMap.dualMap_apply, LinearMap.comp_apply]
    rfl
  rw [h1, hψbar]

end Work.Cohomology
