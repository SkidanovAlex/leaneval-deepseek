import Mathlib
import Submission.Work.CFTLib.fiveTerm_basic

/-!
# The five-term inflation–restriction sequence: exactness in low degrees

Let `π : G' →* G` be a surjective homomorphism with kernel `N = ker π`.  Building on the
vocabulary of `fiveTerm_setup`, this file proves the exactness statements that the dimension
identity of the five-term sequence rests on:

* the cocycle-level inflation is the pullback of functions along `π` (`mapCocycles₂_coe`);
* the transgression `Psi : H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p)`, `t ↦ [candFun t]`, has range the kernel
  of the inflation `H²(G,𝔽_p) → H²(G',𝔽_p)`;
* its kernel is the range of the restriction map `beta`.

The cocycle computations themselves (`candFun` is a cocycle; its inflation is the coboundary of
`auxFun`; the transgression surjects onto the kernel of the inflation; `candFun t` is a
coboundary iff `t` is the restriction of a character of `G'`) are taken as explicit hypotheses
here, so that this file records only the exactness bookkeeping.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

variable (p : ℕ) {G G' : Type} [Group G] [Group G']

/-- The identity morphism `Res(π)(triv G) ⟶ triv G'` along which the inflation map is defined. -/
abbrev inflRep (π : G' →* G) :
    Rep.res π (Rep.trivial (ZMod p) G (ZMod p)) ⟶ Rep.trivial (ZMod p) G' (ZMod p) := 𝟙 _

/-- **Inflation** `H²(G,𝔽_p) → H²(G',𝔽_p)` induced by a surjection `π : G' ↠ G`. -/
abbrev inflMap (π : G' →* G) : H2 p G →ₗ[ZMod p] H2 p G' :=
  (groupCohomology.map π (inflRep p π) 2).hom

/-- The underlying function of the cocycle-level inflation `mapCocycles₂ π 𝟙` is the pullback
along `π`. -/
lemma mapCocycles₂_coe (π : G' →* G) (z : Z2 p G) :
    (groupCohomology.mapCocycles₂ π (inflRep p π) z).1 = precomp₂ π z.1 := by
  have h := groupCohomology.coe_mapCocycles₂
    (A := Rep.trivial (ZMod p) G (ZMod p)) π (inflRep p π) z
  rw [show (groupCohomology.mapCocycles₂ π (inflRep p π) z).1
      = ⇑(groupCohomology.mapCocycles₂ π (inflRep p π) z) from rfl, h]
  ext x
  rfl

variable (π : G' →* G) (hπ : Function.Surjective π)

/-- **The transgression** `H¹(N,𝔽_p)^{G'} → Z²(G,𝔽_p)`, as a linear map into the cocycles. -/
def psi (hcand : ∀ t : invCharSubmodule p π.ker, candFun π hπ t ∈ Z2 p G) :
    invCharSubmodule p π.ker →ₗ[ZMod p] Z2 p G :=
  (candLin π hπ).codRestrict (Z2 p G) hcand

/-- **The transgression** `H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p)`, composing with the quotient map. -/
def Psi (hcand : ∀ t : invCharSubmodule p π.ker, candFun π hπ t ∈ Z2 p G) :
    invCharSubmodule p π.ker →ₗ[ZMod p] H2 p G :=
  (H2pi p G).comp (psi p π hπ hcand)

lemma Psi_apply (hcand) (t : invCharSubmodule p π.ker) :
    Psi p π hπ hcand t = H2pi p G (psi p π hπ hcand t) := rfl

lemma psi_coe (hcand) (t : invCharSubmodule p π.ker) :
    (psi p π hπ hcand t).1 = candFun π hπ t := rfl

/-- The inflation of a transgression cocycle is a coboundary. -/
lemma Psi_mem_ker_infl (hcand)
    (hpre : ∀ t : invCharSubmodule p π.ker,
      precomp₂ π (candFun π hπ t) = d12 p G' (auxFun π hπ t))
    (t : invCharSubmodule p π.ker) : inflMap p π (Psi p π hπ hcand t) = 0 := by
  have h := groupCohomology.H2π_comp_map_apply π (inflRep p π) (psi p π hπ hcand t)
  rw [show inflMap p π (Psi p π hπ hcand t)
      = (groupCohomology.map π (inflRep p π) 2)
          ((groupCohomology.H2π (Rep.trivial (ZMod p) G (ZMod p)))
            (psi p π hπ hcand t)) from rfl,
    h]
  rw [H2pi_eq_zero_iff p G', mapCocycles₂_coe p, psi_coe p, hpre t]
  exact LinearMap.mem_range.mpr ⟨auxFun π hπ t, rfl⟩

/-- The range of the transgression is contained in the kernel of the inflation. -/
lemma range_Psi_le_ker_infl (hcand)
    (hpre : ∀ t : invCharSubmodule p π.ker,
      precomp₂ π (candFun π hπ t) = d12 p G' (auxFun π hπ t)) :
    LinearMap.range (Psi p π hπ hcand) ≤ LinearMap.ker (inflMap p π) :=
  fun _ hy => by
    obtain ⟨t, rfl⟩ := hy
    exact Psi_mem_ker_infl p π hπ hcand hpre t

/-- **The transgression surjects onto the kernel of the inflation.** -/
lemma ker_infl_le_range_Psi (hcand)
    (hex : ∀ (z : G × G → ZMod p), z ∈ Z2 p G → ∀ (b : G' → ZMod p),
      precomp₂ π z = d12 p G' b → ∃ t : invCharSubmodule p π.ker,
        z - candFun π hπ t ∈ B2 p G) :
    LinearMap.ker (inflMap p π) ≤ LinearMap.range (Psi p π hπ hcand) := by
  intro y hy
  rw [LinearMap.mem_ker] at hy
  induction y using groupCohomology.H2_induction_on with
  | h z =>
    rw [LinearMap.mem_range]
    have h1 : (H2pi p G') (groupCohomology.mapCocycles₂ π (inflRep p π) z) = 0 := by
      rw [← groupCohomology.H2π_comp_map_apply π (inflRep p π) z]
      exact hy
    rw [H2pi_eq_zero_iff p G', mapCocycles₂_coe p] at h1
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp h1
    obtain ⟨t, ht⟩ := hex z z.2 b hb.symm
    refine ⟨t, ?_⟩
    have h2 : (H2pi p G) (z - psi p π hπ hcand t) = 0 := by
      rw [H2pi_eq_zero_iff p G]
      exact ht
    rw [map_sub, sub_eq_zero] at h2
    show Psi p π hπ hcand t = H2pi p G z
    rw [show Psi p π hπ hcand t = H2pi p G (psi p π hπ hcand t) from rfl, ← h2]

/-- **The kernel of the transgression is the range of the restriction map.** -/
lemma ker_Psi_eq_range_beta (hcand)
    (hker : ∀ t : invCharSubmodule p π.ker,
      candFun π hπ t ∈ B2 p G ↔ t ∈ LinearMap.range (beta π)) :
    LinearMap.ker (Psi p π hπ hcand) = LinearMap.range (beta π) := by
  ext t
  rw [LinearMap.mem_ker, Psi_apply, H2pi_eq_zero_iff p G, psi_coe p]
  exact hker t

end

end Work.CFTLib
