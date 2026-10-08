import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.CORE2B.L27_fittingPi_sup_compl

/-!
# CORE2B — `F_π(M) ≤ ⨆_{q ∈ π} F_{⟨q⟩}(M)`

For a finite group the `π`-part of the Fitting subgroup is the join of its `q`-parts:

    `F_π(M) ≤ ⨆ (q ∈ π), F_{⟨q⟩}(M)`.

The mathematical content lives in the nilpotent group `F(M)`: there every normal `π`-subgroup
is the join of its Sylow subgroups, each of which lies in `O_{⟨q⟩}(F(M))` for `q ∈ π`.  Indeed,
a `p`-subgroup `X` of a finite nilpotent group `H` is contained in a Sylow `p`-subgroup `Q`,
which is *normal* because `H` is nilpotent; so `X ≤ O_{⟨p⟩}(H)` by the universal property of
the `π`-core.  The statement about `M` follows by mapping along `F(M) ↪ M ↪ G`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-- **Every `p`-subgroup of a finite nilpotent group lies in `O_{⟨p⟩}`.**

`X` is contained in some Sylow `p`-subgroup `Q` (`IsPGroup.exists_le_sylow`); since `H` is
nilpotent, `Q` is normal, and as a `p`-group it is a (normal) `⟨p⟩`-subgroup, so the universal
property of `O_{⟨p⟩}(H)` puts it inside `O_{⟨p⟩}(H)`. -/
theorem le_piCore_singleton_of_isPGroup {H : Type} [Group H] [Finite H] [Group.IsNilpotent H]
    {p : ℕ} [Fact p.Prime] {X : Subgroup H} (hX : IsPGroup p X) :
    X ≤ Work.GW2.piCore ({p} : Set ℕ) H := by
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  haveI : (Q : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent Q
  exact hXQ.trans (le_piCore_of_normal_isPiSubgroup_gw (G := H) (π := ({p} : Set ℕ))
    (N := (Q : Subgroup H))
    (Subgroup.isPiSubgroup_of_isPGroup_of_mem Q.isPGroup' (Set.mem_singleton p)))

/-- **`O_π(H) ≤ ⨆_{q ∈ π} O_{⟨q⟩}(H)` for a finite nilpotent group `H`.**

`O_π(H)` is the normal core of the join of the normal `π`-subgroups of `H`, so it suffices to
place each normal `π`-subgroup `N ≤ H` inside the right-hand side.  `N` is nilpotent (a
subgroup of `H`), hence the join of its own Sylow subgroups
(`iSup_default_sylow_eq_top_of_nilpotent`); each Sylow `p`-subgroup of `N`, pushed into `H`, is
a `p`-subgroup with `p ∈ π` (as `N` is a `π`-subgroup), and therefore lies in `O_{⟨p⟩}(H)` by
`le_piCore_singleton_of_isPGroup`. -/
theorem piCore_le_iSup_piCore_singleton {H : Type} [Group H] [Finite H] [Group.IsNilpotent H]
    (π : Set ℕ) :
    Work.GW2.piCore π H ≤ ⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.piCore ({q} : Set ℕ) H := by
  rw [Work.GW2.piCore]
  refine (Subgroup.normalCore_le _).trans (sSup_le ?_)
  rintro N ⟨hNnorm, hNpi⟩
  haveI := hNnorm
  have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop, ← OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N,
    Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hpPi : p ∈ π := hNpi p hp
  have himg : IsPGroup p (((default : Sylow (p : ℕ) ↥N) : Subgroup ↥N).map N.subtype) :=
    IsPGroup.map (default : Sylow (p : ℕ) ↥N).isPGroup' N.subtype
  refine (le_piCore_singleton_of_isPGroup himg).trans ?_
  exact (le_iSup (fun (_ : p ∈ π) => Work.GW2.piCore ({p} : Set ℕ) H) hpPi).trans
    (le_iSup (fun q => ⨆ (_ : q ∈ π), Work.GW2.piCore ({q} : Set ℕ) H) p)

theorem L27_fittingPiIn_le_iSup_singleton {G : Type} [Group G] [Finite G] (π : Set ℕ)
    (M : Subgroup G) :
    Work.GW2.fittingPiIn π M ≤ ⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.fittingPiIn ({q} : Set ℕ) M := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥M) := L27cf_isNilpotent_fitting
  have key : Work.GW2.piCore π ↥(Work.GW2.fitting ↥M) ≤
      ⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.piCore ({q} : Set ℕ) ↥(Work.GW2.fitting ↥M) :=
    piCore_le_iSup_piCore_singleton π
  have hmono : (Work.GW2.piCore π ↥(Work.GW2.fitting ↥M)).map
        (Work.GW2.fitting ↥M).subtype ≤
      ((⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.piCore ({q} : Set ℕ) ↥(Work.GW2.fitting ↥M)).map
        (Work.GW2.fitting ↥M).subtype) :=
    Subgroup.map_mono key
  simp only [Work.GW2.fittingPiIn, Work.GW2.fittingPi]
  refine (Subgroup.map_mono hmono).trans (le_of_eq ?_)
  simp only [Subgroup.map_iSup]

end Work.CORE2B
