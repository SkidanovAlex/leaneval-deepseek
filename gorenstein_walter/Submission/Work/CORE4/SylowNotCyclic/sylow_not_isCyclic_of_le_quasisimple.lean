import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic

set_option linter.style.haveILetI false

namespace Work.CORE4.SylowNotCyclic

/-- If `E ≤ M` is quasisimple, then no Sylow `2`-subgroup of `M` is cyclic.

Route: a Sylow `2`-subgroup `P₀` of `↥E` is non-cyclic
(`Work.CORE4.NineQuasisimpleSylowNotCyclic`, in `Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic`);
its image `X` under `Subgroup.inclusion hEM : ↥E →* ↥M` is a `2`-subgroup of `↥M`
(`IsPGroup.map`), so it lies in some Sylow `Q` of `↥M` (`IsPGroup.exists_le_sylow`); `↥X ≃* ↥P₀`
(`Subgroup.equivMapOfInjective`) so `Q` is not cyclic either (a subgroup of a cyclic group is
cyclic).  Finally every Sylow `P` of `↥M` is isomorphic to `Q` (`Sylow.equiv P Q`, using the
instance `Finite (Sylow 2 ↥M)`), and `IsCyclic` is transported by `MulEquiv.isCyclic`. -/
theorem sylow_not_isCyclic_of_le_quasisimple {G : Type} [Group G] [Finite G]
    {E M : Subgroup G} (hE : Work.GW2.IsQuasisimple E) (hEM : E ≤ M) :
    ∀ P : Sylow 2 ↥M, ¬ IsCyclic ↥(P : Subgroup ↥M) := by
  intro P hcycP
  haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- A Sylow `2`-subgroup `P₀` of `↥E`, and its image `X` in `↥M`.
  obtain ⟨P₀⟩ := Sylow.nonempty (p := 2) (G := ↥E)
  set X : Subgroup ↥M := (P₀ : Subgroup ↥E).map (Subgroup.inclusion hEM) with hXdef
  have hXp : IsPGroup 2 X := P₀.isPGroup'.map (Subgroup.inclusion hEM)
  obtain ⟨Q, hXQ⟩ := hXp.exists_le_sylow
  -- `Q` is not cyclic: otherwise its subgroup `X ≅ P₀` would be cyclic, hence so would `P₀`.
  have hQnc : ¬ IsCyclic ↥(Q : Subgroup ↥M) := by
    intro hQcyc
    haveI := hQcyc
    have hXcyc : IsCyclic ↥X := Subgroup.isCyclic_of_le hXQ
    have hP₀cyc : IsCyclic ↥(P₀ : Subgroup ↥E) :=
      (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (P₀ : Subgroup ↥E)
        (Subgroup.inclusion hEM) (Subgroup.inclusion_injective hEM))).mpr hXcyc
    exact Work.CORE4.NineQuasisimpleSylowNotCyclic hE P₀ hP₀cyc
  -- Every Sylow of `↥M` is isomorphic to `Q`, so none is cyclic.
  exact hQnc ((MulEquiv.isCyclic (Sylow.equiv P Q)).mp hcycP)

end Work.CORE4.SylowNotCyclic
