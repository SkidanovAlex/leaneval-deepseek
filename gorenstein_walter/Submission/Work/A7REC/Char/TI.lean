/-
Area `A7REC`, file `Char/TI.lean`: the TI-subset normalizer bounds of design pass 6
(`_design_gw/Core6.lean` §2), which replace Suzuki's Brauer blocks in the derivation of the
degree-`6` character.

* `a7TIOrderFour` : for `π ∈ S` of order `4` with `C_G(π) = ⟨π⟩` and `N_G(⟨π⟩) = S`, any element
  conjugating `π` to `π^{±1}` lies in `S`.  (This is the normalizer half of "`{π, π⁻¹}` is a TI
  subset"; the substantive input `N_G(⟨π⟩) = S` is A1
  `Work.A7REC.Basic.exists_tau_order_four`.)
-/
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Basic.exists_tau_order_four

namespace Work.A7REC

open Subgroup

/-- **The TI normalizer bound for `{π, π⁻¹}`** (design pass 6, `A7TIOrderFourProp`).

If `π` has order `4`, `C_G(π) = ⟨π⟩` and `N_G(⟨π⟩) = S`, then every `g` with
`g π g⁻¹ ∈ {π, π⁻¹}` lies in `S`: in the first case `g ∈ C_G(π) = ⟨π⟩ ≤ S` (as `π ∈ S`); in the
second case `g` normalizes `⟨π⟩`, so `g ∈ N_G(⟨π⟩) = S`. -/
theorem a7TIOrderFour : A7TIOrderFourProp := by
  intro G _ _ S π hπ _hord hC hN g hg
  rcases hg with hg | hg
  · -- `g * π * g⁻¹ = π`: `g` centralizes `π`
    have hcomm : g * π = π * g := by
      have h := congrArg (fun x => x * g) hg
      simpa [mul_assoc] using h
    have hmem : g ∈ Subgroup.centralizer ({π} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm.symm
    rw [hC] at hmem
    exact Subgroup.zpowers_le.mpr hπ hmem
  · -- `g * π * g⁻¹ = π⁻¹`: `g` normalizes `⟨π⟩`
    have hmap : (Subgroup.zpowers π).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers π := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (g * π * g⁻¹) = Subgroup.zpowers π
      rw [hg, Subgroup.zpowers_inv]
    rw [← hN]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

end Work.A7REC
