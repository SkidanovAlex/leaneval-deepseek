import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.FittingInConj
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent

namespace Work.CORE4.FittingMonotone

/-- **`F(K) ≤ F(X)` when `X` normalizes `K`**: if `K ≤ X` and `X ≤ N_G(K)`, then the Fitting
subgroup of `K` realized in the ambient group is contained in that of `X`.

Route (all the ingredients already exist in area CORE4 — do NOT import
`Submission.Work.CORE2B.*`, it declares the same `Work.GW2` vocabulary):

* `X ≤ N_G(fittingIn K)` (the `C ≤ N_G(K) → C ≤ N_G(F(K))` step, here with `C := X`): for
  `x ∈ X` one has `K.map (MulAut.conj x) = K` (`Subgroup.mem_normalizer_iff_map_conj_eq`),
  so `(fittingIn K).map (MulAut.conj x) = fittingIn (K.map (MulAut.conj x)) = fittingIn K` by
  `Work.CORE4.FittingInConj` (`Submission/Work/CORE4/FittingInConj.lean`);
* `(fittingIn K).subgroupOf X` is normal in `↥X`
  (`Subgroup.normal_subgroupOf_iff_le_normalizer`), and `Group.IsNilpotent ↥(fittingIn K)` is
  `Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn K`
  (`Submission/Work/CORE4/SevenX/piFU_le_pi_K0F.lean`, Fitting's theorem);
* conclude with
  `Work.CORE4.FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent`
  (`Submission/Work/CORE4/FpropsAux/mem_fittingIn_of_le_of_normal_isNilpotent.lean`), applied to
  `Y := fittingIn K`, `M₀ := X`, using `fittingIn K ≤ K ≤ X`
  (`Subgroup.map_subtype_le`). -/
theorem fittingIn_le_fittingIn_of_le_normalizer {G : Type} [Group G] [Finite G]
    {K X : Subgroup G} (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    Work.GW2.fittingIn K ≤ Work.GW2.fittingIn X := by
  -- `X` normalizes `F(K)`: conjugation by `x ∈ X` fixes `K`, hence fixes `F(K)` (characteristic)
  have hXnormF : X ≤ Subgroup.normalizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) := by
    intro x hx
    have hmapK : K.map (MulAut.conj x).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXK hx)
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    change Subgroup.map (MulAut.conj x).toMonoidHom (Work.GW2.fittingIn K) = Work.GW2.fittingIn K
    rw [← Work.CORE4.FittingInConj K (MulAut.conj x), hmapK]
  -- `F(K)` lies in `X`, and is normal in `↥X` and nilpotent
  have hle : Work.GW2.fittingIn K ≤ X :=
    (Subgroup.map_subtype_le (Work.GW2.fitting ↥K)).trans hKX
  have hNorm : ((Work.GW2.fittingIn K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hXnormF
  have hNil : Group.IsNilpotent ↥(Work.GW2.fittingIn K) :=
    Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn K
  -- being a normal nilpotent subgroup of `X`, it is contained in `F(X)`
  intro y hy
  exact Work.CORE4.FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent hle hNorm hNil hy

end Work.CORE4.FittingMonotone
