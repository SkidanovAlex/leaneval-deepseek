import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilG4b

open WilkiesDesign

/-! ## An infinite preconnected subset of `ℝ` contains an open interval

This is the purely topological (o-minimal) input: a preconnected set in `ℝ` with two distinct
points contains the closed interval between them, and an infinite set has two distinct points. -/

lemma exists_Ioo_subset_of_isPreconnected_infinite {A : Set ℝ} (hA : IsPreconnected A)
    (hinf : A.Infinite) : ∃ c d : ℝ, c < d ∧ Set.Ioo c d ⊆ A := by
  obtain ⟨a, ha⟩ := hinf.nonempty
  have hex : ∃ b ∈ A, b ≠ a := by
    by_contra h
    push Not at h
    exact hinf ((Set.finite_singleton a).subset fun y hy => by simpa using h y hy)
  obtain ⟨b, hb, hba⟩ := hex
  rcases lt_or_gt_of_ne hba with hlt | hlt
  · exact ⟨b, a, hlt, fun t ht => hA.Icc_subset hb ha ⟨ht.1.le, ht.2.le⟩⟩
  · exact ⟨a, b, hlt, fun t ht => hA.Icc_subset ha hb ⟨ht.1.le, ht.2.le⟩⟩

/-- In dimension one, the elementary `S.comps` construction of a sharply o-minimal structure
(`S.Ω F D 1` is a finite union of preconnected sets) forces an infinite such set to contain a
whole open interval of the `t`-axis. The sharp cell-decomposition hypothesis is not needed. -/
theorem infinite_contains_Ioo (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {F D : ℕ}
    {X : Set (Fin 1 → ℝ)} (hX : X ∈ S.Ω F D 1) (hinf : X.Infinite) :
    ∃ c d : ℝ, c < d ∧ ∀ t : ℝ, c < t → t < d → (fun _ : Fin 1 => t) ∈ X := by
  -- `X` is a finite union of preconnected sets
  obtain ⟨p, hp⟩ := S.comps F
  obtain ⟨s, -, hconn, hsX⟩ := hp D X hX
  -- one of the pieces is infinite
  have hex : ∃ c ∈ s, c.Infinite := by
    by_contra h
    push Not at h
    have hfin : (⋃₀ (s : Set (Set (Fin 1 → ℝ)))).Finite :=
      (Finset.finite_toSet s).sUnion fun t ht => h t (Finset.mem_coe.mp ht)
    exact hinf (hsX.symm ▸ hfin)
  obtain ⟨c, hc_mem, hc_inf⟩ := hex
  have hc_conn : IsPreconnected c := hconn c hc_mem
  -- push the infinite preconnected piece down to the `t`-axis
  set A : Set ℝ := (fun x : Fin 1 → ℝ => x 0) '' c with hAdef
  have hinj : Set.InjOn (fun x : Fin 1 → ℝ => x 0) c := by
    intro x _ y _ hxy
    funext i
    rw [Subsingleton.elim i 0]
    exact hxy
  have hAinf : A.Infinite := by rw [hAdef]; exact hc_inf.image hinj
  have hAconn : IsPreconnected A := by
    rw [hAdef]; exact hc_conn.image _ (continuous_apply 0).continuousOn
  obtain ⟨a, b, hab, hIoo⟩ := exists_Ioo_subset_of_isPreconnected_infinite hAconn hAinf
  refine ⟨a, b, hab, fun t ht1 ht2 => ?_⟩
  have htA : t ∈ A := hIoo ⟨ht1, ht2⟩
  rw [hAdef] at htA
  obtain ⟨x, hxc, hx0⟩ := htA
  have hxt : (fun _ : Fin 1 => t) = x := by
    funext i
    rw [Subsingleton.elim i 0]
    exact hx0.symm
  rw [hxt, hsX]
  exact Set.mem_sUnion.mpr ⟨c, Finset.mem_coe.mpr hc_mem, hxc⟩

end Work.WilG4b
