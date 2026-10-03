import Mathlib

namespace Work.ORFlatness

universe u

set_option linter.style.haveILetI false

/-- Every left `K[G]`-module carries a `K`-module structure compatible with the `K[G]`-action (and with the ring map `algebraMap K (MonoidAlgebra K G)`), namely the restriction of scalars along `K → K[G]`. This is used to reduce statements quantified over left `K[G]`-modules that carry a compatible `K`-module structure to statements about all left `K[G]`-modules.

Concretely, `inst` should be `Module.compHom M (algebraMap K (MonoidAlgebra K G))` (i.e. `k • m := (algebraMap K (MonoidAlgebra K G) k) • m`); `IsScalarTower K K[G] M` is then associativity of the `K[G]`-action, and `SMulCommClass K K[G] M` expresses that the image of `K` is central in `K[G]` (`Algebra.commutes`).

Hint for the proof: because the compatibility conditions mention the `SMul K M` instance *inside* the proposition, bind it first with `letI : Module K M := Module.compHom M (algebraMap K (MonoidAlgebra K G))` (or `let`), and *then* `refine ⟨Module.compHom M (algebraMap K (MonoidAlgebra K G)), ?_⟩`; `Module.compHom_apply` does not exist, the smul is `rfl`-equal to `algebraMap k • ·`. -/
theorem exists_compatibleKStructure (K : Type u) [CommRing K] (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M] :
    ∃ (inst : Module K M), (letI := inst;
      IsScalarTower K (MonoidAlgebra K G) M ∧ SMulCommClass K (MonoidAlgebra K G) M) := by
  -- Restriction of scalars along `K → K[G]`: `k • m = algebraMap K K[G] k • m`.
  letI : Module K M := Module.compHom M (algebraMap K (MonoidAlgebra K G))
  refine ⟨Module.compHom M (algebraMap K (MonoidAlgebra K G)),
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl), ?_⟩
  -- `SMulCommClass K K[G] M`: the `K`-action is central in `K[G]`.
  refine ⟨fun x y z => ?_⟩
  show (algebraMap K (MonoidAlgebra K G) x) • (y • z) =
    y • ((algebraMap K (MonoidAlgebra K G) x) • z)
  rw [← mul_smul, ← mul_smul, Algebra.commutes (R := K) x y]

end Work.ORFlatness
