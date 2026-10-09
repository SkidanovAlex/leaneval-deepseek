import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.coboundary2_top_of_coboundary2_on_coprime_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **A locally constant `2`-cocycle on a pro-prime-to-`p` compact group is a coboundary.**

`Γ` a compact Hausdorff topological group all of whose finite quotients have order prime to `p`
(`Work.SSGRoute.IsProPrimeToP p Γ`), `act : Γ →* G` a homomorphism into a group `G` acting on a
finite `𝔽_p`-module `N`.  Then every `Γ`-invariant (`SSGRoute.IsCocycle2`) locally constant
(`SSGRoute.IsLocConst2`) `2`-cocycle `c : Γ → Γ → N` is the coboundary of a locally constant
`1`-cochain: `SSGRoute.IsCoboundary2On act ⊤ c`.

Route: take an open subgroup `U₀ ≤ Γ` under which `c` is invariant (from `IsLocConst2`; `U₀` has
finite index since `Γ` is compact), let `U := U₀.normalCore` (open, normal, finite index, index
coprime to `p` by `IsProPrimeToP`), and put `B g := (1/[Γ:U]) · Σ_{x ∈ Γ/U} c g x` (finite sum
over coset representatives; the index is invertible in `𝔽_p`).  The cocycle identity gives
`δB = c`, and `B` is `U`-invariant, hence locally constant.

Useful on disk: `Work.SSGRoute.cob2_average`, `Work.SSGRoute.cob2d`,
`Work.SSGRoute.cob2_isCocycle2_sub` in
`Submission/Work/SSGRoute/coboundary2_top_of_coboundary2_on_coprime_index.lean`, and
`Work.SSGRoute.coboundaries_le_lcCocycles`, `Work.SSGRoute.cob2_average`. -/
theorem isCoboundary2On_top_of_isProPrimeToP
    (p : ℕ) [Fact p.Prime] {Γ G N : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [Group G] [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction G N] [SMulCommClass G (ZMod p) N] [Finite N]
    (hpro : Work.SSGRoute.IsProPrimeToP p Γ) (act : Γ →* G) (c : Γ → Γ → N)
    (hc : _root_.SSGRoute.IsCocycle2 act c) (hlc : _root_.SSGRoute.IsLocConst2 c) :
    _root_.SSGRoute.IsCoboundary2On act ⊤ c := by
  classical
  -- An open subgroup of `Γ` under which `c` is invariant.
  obtain ⟨U₀, hU₀open, hU₀inv⟩ := hlc
  -- `U₀` is clopen (open subgroups are closed), so it contains an open *normal* subgroup `H`.
  have hU₀clopen : IsClopen (U₀ : Set Γ) :=
    ⟨Subgroup.isClosed_of_isOpen U₀ hU₀open, hU₀open⟩
  obtain ⟨H, hHle⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hU₀clopen U₀.one_mem
  -- `H` has finite index (open subgroup of a compact group) and index coprime to `p`.
  haveI : Finite (Γ ⧸ H.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen H.toSubgroup H.toOpenSubgroup.isOpen
  haveI hHfin : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcop : Nat.Coprime H.toSubgroup.index p := (hpro H.toSubgroup hHfin).symm
  -- `c` is invariant under right multiplication by `H` in each variable.
  have hHle' : ∀ x ∈ H.toSubgroup, x ∈ U₀ := fun x hx => hHle hx
  have h1mem : (1 : Γ) ∈ U₀ := hHle' 1 H.toSubgroup.one_mem
  have hinv2 : ∀ a b : Γ, ∀ h ∈ H.toSubgroup, c a (b * h) = c a b := by
    intro a b h hh
    have h1 := hU₀inv a b 1 h h1mem (hHle' h hh)
    simpa using h1
  have hinv1 : ∀ a b : Γ, ∀ h ∈ H.toSubgroup, c (a * h) b = c a b := by
    intro a b h hh
    have h1 := hU₀inv a b h 1 (hHle' h hh) h1mem
    simpa using h1
  -- Average `c` over the finite quotient `Γ ⧸ H`: this produces the primitive `B`.
  obtain ⟨B, hBinv, hBeq⟩ :=
    cob2_average p act H.toSubgroup hcop H.toSubgroup c hc hinv2 hinv1
  refine ⟨B, ?_, ?_⟩
  · exact ⟨H.toSubgroup, H.toOpenSubgroup.isOpen, fun g _ v hv _ => hBinv g v hv⟩
  · intro g _ h _
    exact (hBeq g h).symm

end Work.SSGRoute
