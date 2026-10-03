import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Param.baire_closed_cover
import Submission.Work.Repel.iterate_diffAt
import Submission.Work.Repel.liftSel_def
import Submission.Work.Repel.baire_open_subset
import Submission.Work.Repel.liftSel_differentiableOn
import Submission.Work.Repel.iterate_comp_phi

/-!
# The "(4.2.3)-Moreover" uniform-iterate statement for the perturbed return map

Shishikura §6, Step 6 needs the *set-level* ("Moreover") clause of (4.2.3): the return map `R̃_f`
composed with the perturbed Fatou coordinates around a full revolution is a genuine iterate `f^n`
of `f`, with `n` depending only on the revolution, not on the point.  The interface field
`MandelDim.PertData.orbit` gives the pointwise form only.

The point is that the pointwise `n` is *locally constant*: the sets
`Z_k = {w ∈ U | f^[k] (φ_f w) = φ_f (w'(w))}` (where `w'(w)` is the point of `U'` with
`π w'(w) = π (R̃_f^m w)`, unique because `π` is injective on `U'`) are closed in `U` and cover `U`;
`U` is an open subset of the Baire space `ℂ`, so some `Z_k` is somewhere dense in `U`; the
holomorphic function `G_k = f^[k] ∘ φ_f - φ_f ∘ w'` therefore vanishes on a whole neighbourhood of
a point of `U`, and the identity theorem on the connected open set `U` gives `G_k ≡ 0`, i.e. a
uniform iterate `k ≥ 1`.  This is exactly the form in which §6 Step 6 consumes (4.2.3).
-/

set_option linter.style.haveILetI false

namespace Work.Repel

theorem pert_orbit_eqOn {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} {f : ℂ → ℂ} {Df : Set ℂ}
    {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ} (P : MandelDim.PertData d f Df η y₁ K K' δ)
    (hDfopen : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    {U U' : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUsub : U ⊆ P.Dφ)
    (hU'o : IsOpen U') (hU'sub : U' ⊆ P.Dφ) (hinj : Set.InjOn MandelDim.piExp U')
    {m : ℕ} (hm : 1 ≤ m)
    (hwalk : ∀ w ∈ U, ∀ j < m, P.R^[j] w ∈ P.DR)
    (hmaps : ∀ w ∈ U, MandelDim.piExp (P.R^[m] w) ∈ MandelDim.piExp '' U')
    (hangle : ∀ w ∈ U, ∀ w' ∈ U',
      |Complex.arg (w' + 1 / (2 * MandelDim.rotOf f) - w)| < 2 * Real.pi / 3)
    (hiter : ∀ w ∈ U, ∀ j : ℕ, f^[j] (P.φ w) ∈ Df) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ w ∈ U, ∀ w' ∈ U',
      MandelDim.piExp w' = MandelDim.piExp (P.R^[m] w) → f^[n] (P.φ w) = P.φ w' := by
  classical
  by_cases hUne : U.Nonempty
  · -- the point of `U'` with the same `π`-image as `R̃_f^m w`, as a function of `w`
    set W : ℂ → ℂ := liftSel P.R m U' with hWdef
    have hwit : ∀ w ∈ U, ∃ w' ∈ U', MandelDim.piExp w' = MandelDim.piExp (P.R^[m] w) := by
      intro w hw
      have hmem := hmaps w hw
      rw [Set.mem_image] at hmem
      obtain ⟨w', hw', hpi⟩ := hmem
      exact ⟨w', hw', hpi⟩
    have hWspec : ∀ w ∈ U, W w ∈ U' ∧ MandelDim.piExp (W w) = MandelDim.piExp (P.R^[m] w) := by
      intro w hw
      rw [hWdef]
      exact liftSel_spec (hwit w hw)
    have hWdiff : DifferentiableOn ℂ W U := by
      rw [hWdef]
      exact liftSel_differentiableOn P hUo hU'o hinj hm hwalk hmaps
    -- the holomorphic functions whose zero sets carry the pointwise iterate
    set G : ℕ → ℂ → ℂ := fun k w => f^[k] (P.φ w) - P.φ (W w) with hGdef
    have hGval : ∀ k : ℕ, G k = fun w => f^[k] (P.φ w) - P.φ (W w) := fun k => rfl
    have hGdiff : ∀ k : ℕ, DifferentiableOn ℂ (G k) U := by
      intro k
      rw [hGval k]
      have h1 : DifferentiableOn ℂ (fun w => f^[k] (P.φ w)) U :=
        iterate_comp_phi P hDfopen hf hUsub hiter k
      have h2 : DifferentiableOn ℂ (fun w => P.φ (W w)) U :=
        P.φ_holo.comp hWdiff (fun w hw => hU'sub (hWspec w hw).1)
      refine (h1.sub h2).congr ?_
      intro w hw
      rw [Pi.sub_apply]
    -- the closed covering of `U` given by the pointwise (4.2.3)
    have hcover : (Set.univ : Set ↥U) ⊆ ⋃ n, {u : ↥U | G (n + 1) (u : ℂ) = 0} := by
      intro u _
      have hu : (u : ℂ) ∈ U := u.2
      obtain ⟨n, hn1, hn2, -⟩ :=
        P.orbit (u : ℂ) (hUsub hu) (W (u : ℂ)) (hU'sub (hWspec (u : ℂ) hu).1) m hm
          (hwalk (u : ℂ) hu) (hWspec (u : ℂ) hu).2.symm
          (hangle (u : ℂ) hu (W (u : ℂ)) (hWspec (u : ℂ) hu).1)
      refine Set.mem_iUnion.mpr ⟨n - 1, ?_⟩
      show G (n - 1 + 1) (u : ℂ) = 0
      rw [Nat.sub_add_cancel hn1]
      show f^[n] (P.φ (u : ℂ)) - P.φ (W (u : ℂ)) = 0
      rw [hn2, sub_self]
    have hZcl : ∀ n : ℕ, ∃ K : Set ↥U, IsClosed K ∧
        ({u : ↥U | G (n + 1) (u : ℂ) = 0} : Set ↥U) = Set.univ ∩ K := by
      intro n
      refine ⟨(fun u : ↥U => G (n + 1) (u : ℂ)) ⁻¹' {0}, ?_, ?_⟩
      · have hcont : Continuous (fun u : ↥U => G (n + 1) (u : ℂ)) :=
          (hGdiff (n + 1)).continuousOn.domRestrict
        exact isClosed_singleton.preimage hcont
      · ext u; simp
    -- Baire: one of the zero sets is somewhere dense in `U`
    haveI : Nonempty ↥U := hUne.to_subtype
    haveI : BaireSpace ↥U := hUo.baireSpace
    obtain ⟨n, V, hVopen, hVne, hVsub⟩ :=
      baire_open_subset (X := ↥U) (U := Set.univ) isOpen_univ Set.univ_nonempty hZcl hcover
    simp only [Set.inter_univ] at hVne hVsub
    -- an open neighbourhood of a point of `U` on which `G (n+1)` vanishes
    obtain ⟨u₀, hu₀V⟩ := hVne
    have hxU : (u₀ : ℂ) ∈ U := u₀.2
    have hev : G (n + 1) =ᶠ[nhds (u₀ : ℂ)] 0 := by
      have hmem : V ∈ nhds u₀ := hVopen.mem_nhds hu₀V
      rw [nhds_subtype] at hmem
      obtain ⟨W', hW'mem, hW'sub⟩ := Filter.mem_comap.mp hmem
      filter_upwards [Filter.inter_mem hW'mem (hUo.mem_nhds hxU)] with z hz
      exact hVsub (hW'sub (show (⟨z, hz.2⟩ : ↥U) ∈ Subtype.val ⁻¹' W' from hz.1))
    -- identity theorem: the uniform iterate
    have hGan : AnalyticOnNhd ℂ (G (n + 1)) U :=
      (Complex.analyticOnNhd_iff_differentiableOn hUo).mpr (hGdiff (n + 1))
    have hEqOn : Set.EqOn (G (n + 1)) 0 U :=
      hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected hxU hev
    refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
    intro w hw w' hw' hpi
    have hgw : G (n + 1) w = 0 := hEqOn hw
    have hres : f^[n + 1] (P.φ w) = P.φ (W w) := by
      have h0 : f^[n + 1] (P.φ w) - P.φ (W w) = 0 := hgw
      exact sub_eq_zero.mp h0
    have hWW : W w = w' := by
      refine hinj (hWspec w hw).1 hw' ?_
      rw [hpi]
      exact (hWspec w hw).2
    rw [hWW] at hres
    exact hres
  · -- `U = ∅`: any iterate works
    refine ⟨1, le_refl 1, fun w hw => ?_⟩
    exact absurd ⟨w, hw⟩ hUne

end Work.Repel
