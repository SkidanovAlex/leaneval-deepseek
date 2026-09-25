import Mathlib
import Submission.Work.RelatorRank.Gaschutz.frattini_nongenerating_of_fg

/-!
# Gaschütz's non-generator property, relative form

**Namespace** `Work.RelatorRank.Gaschutz`; module
`Submission.Work.RelatorRank.Gaschutz.eq_of_normalClosure_sup_frattini_eq_top`.

The classical non-generator property of the Frattini subgroup (`frattini_nongenerating`,
and its finitely generated form `Work.RelatorRank.Gaschutz.frattini_nongenerating_of_fg`)
says that a subgroup `H` of a group `G` with `H ⊔ frattini G = ⊤` is all of `G`, provided
`G` is finitely generated.

Here we need the *relative* form: `R` is a subgroup of an ambient group `F`, `N ≤ R` is a
subgroup of `F` contained in `R`, and `N` together with (the image in `F` of) the Frattini
subgroup of `R` generates `R`; then `N = R`.  The proof transports the statement from `F`
to the group `↥R` along the injective monoid homomorphism `R.subtype`: mapping subgroups of
`↥R` into `F` along `R.subtype` is injective and commutes with `⊔`, so the hypothesis
becomes `N.subgroupOf R ⊔ frattini R = ⊤` inside `↥R`, to which the non-generator property
applies because `↥R` is finitely generated.
-/

namespace Work.RelatorRank.Gaschutz

/-- **Relative Gaschütz non-generator property.**  Let `R` be a finitely generated subgroup
of a group `F` and let `N ≤ R`.  If `N` together with the image in `F` of the Frattini
subgroup of `R` generates `R`, then already `N = R`. -/
theorem eq_of_normalClosure_sup_frattini_eq_top {F : Type*} [Group F] (R : Subgroup F) [Group.FG R]
    (N : Subgroup F) (hN : N ≤ R) (h : N ⊔ Subgroup.map R.subtype (frattini R) = R) : N = R := by
  -- Work inside the group `↥R`, where `N` becomes `M := N.subgroupOf R`.
  set M : Subgroup R := N.comap R.subtype with hMdef
  -- `M` maps back onto `N` along `R.subtype`, since `N ≤ R = R.subtype.range`.
  have hmap : M.map R.subtype = N :=
    Subgroup.map_comap_eq_self (f := R.subtype) (H := N) (by rwa [Subgroup.range_subtype])
  -- The whole of `↥R` maps onto `R`.
  have htop : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← Subgroup.subgroupOf_self R]
    exact Subgroup.map_comap_eq_self (f := R.subtype) (H := R) (by rw [Subgroup.range_subtype])
  -- Transport the hypothesis into `↥R`; `Subgroup.map R.subtype` is injective.
  have hsup : M ⊔ frattini R = ⊤ := by
    rw [← Subgroup.map_subtype_inj (H := R)]
    rw [Subgroup.map_sup, hmap, htop, h]
  -- Gaschütz's non-generator property in the finitely generated group `↥R`.
  have hMtop : M = ⊤ := frattini_nongenerating_of_fg (G := R) ‹Group.FG R› M hsup
  rw [← hmap, hMtop, htop]

end Work.RelatorRank.Gaschutz
