import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.pert_orbit_eqOn
import Submission.Work.Repel.baire_avoid
import Submission.Work.Repel.interior_zero_set_holo

/-!
# The uniform-iterate form of (4.2.3) with a point-dependent return count

Shishikura §6, Step 6 consumes the "(4.2.3) Moreover" clause in the following shape: on an open
connected source region `U` the perturbed return map `R̃_f`, raised to a *pointwise* return count
`m w`, agrees with a genuine iterate `f^n` of `f` of a *fixed* length `n`, uniformly over `U`.

The interface field `MandelDim.PertData.orbit` gives only the pointwise statement (for each `w`
there is `n = n w` with `f^{n w} (φ_f w) = φ_f (w'(w))`).  Here `w' : ℂ → ℂ` is any holomorphic
map `U → Dφ_f` with `π (w'(w)) = π (R̃_f^{m w} w)` and the angle condition of (4.2.3).

The pointwise count is upgraded to a uniform one by Baire category: the sets
`Z_k = {w ∈ U | f^[k] (φ w) = φ (w' w)}` are closed in `U` and cover `U`, so some `Z_k` is
somewhere dense in `U`; the holomorphic function `G_k = f^[k] ∘ φ - φ ∘ w'` therefore vanishes on
a non-empty open subset of the connected open set `U`, and the identity theorem gives `G_k ≡ 0`.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

theorem uniform_iterate_of_orbit
    {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} {f : ℂ → ℂ} {Df : Set ℂ}
    {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ} (P : MandelDim.PertData d f Df η y₁ K K' δ)
    (hDfopen : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUsub : U ⊆ P.Dφ)
    (w' : ℂ → ℂ) (hw'diff : DifferentiableOn ℂ w' U) (hw'sub : ∀ w ∈ U, w' w ∈ P.Dφ)
    (m : ℂ → ℕ) (hm1 : ∀ w ∈ U, 1 ≤ m w)
    (hwalk : ∀ w ∈ U, ∀ j < m w, P.R^[j] w ∈ P.DR)
    (hpi : ∀ w ∈ U, MandelDim.piExp (P.R^[m w] w) = MandelDim.piExp (w' w))
    (hangle : ∀ w ∈ U, |Complex.arg (w' w + 1 / (2 * MandelDim.rotOf f) - w)| < 2 * Real.pi / 3)
    (hiter : ∀ w ∈ U, ∀ j : ℕ, f^[j] (P.φ w) ∈ Df) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ w ∈ U, f^[n] (P.φ w) = P.φ (w' w) := by
  classical
  by_cases hUne : U.Nonempty
  · -- the holomorphic functions whose zero sets carry the pointwise iterate
    set G : ℕ → ℂ → ℂ := fun k w => f^[k] (P.φ w) - P.φ (w' w) with hGdef
    have hGdiff : ∀ k : ℕ, DifferentiableOn ℂ (G k) U := by
      intro k
      have h1 : DifferentiableOn ℂ (fun w => f^[k] (P.φ w)) U :=
        iterate_comp_phi P hDfopen hf hUsub hiter k
      have h2 : DifferentiableOn ℂ (fun w => P.φ (w' w)) U :=
        P.φ_holo.comp hw'diff hw'sub
      exact h1.sub h2
    -- the closed covering of `U` given by the pointwise (4.2.3)
    have hcover : (Set.univ : Set ↥U) ⊆ ⋃ n : ℕ, {u : ↥U | G (n + 1) (u : ℂ) = 0} := by
      intro u _
      have hu : (u : ℂ) ∈ U := u.2
      obtain ⟨n, hn1, hn2, -⟩ :=
        P.orbit (u : ℂ) (hUsub hu) (w' (u : ℂ)) (hw'sub (u : ℂ) hu) (m (u : ℂ))
          (hm1 (u : ℂ) hu) (hwalk (u : ℂ) hu) (hpi (u : ℂ) hu) (hangle (u : ℂ) hu)
      refine Set.mem_iUnion.mpr ⟨n - 1, ?_⟩
      show G (n - 1 + 1) (u : ℂ) = 0
      rw [Nat.sub_add_cancel hn1]
      show f^[n] (P.φ (u : ℂ)) - P.φ (w' (u : ℂ)) = 0
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
    intro w hw
    have hgw : G (n + 1) w = 0 := hEqOn hw
    have h0 : f^[n + 1] (P.φ w) - P.φ (w' w) = 0 := hgw
    exact sub_eq_zero.mp h0
  · -- `U = ∅`: any iterate works
    refine ⟨1, le_refl 1, fun w hw => ?_⟩
    exact absurd ⟨w, hw⟩ hUne

end Work.Repel
