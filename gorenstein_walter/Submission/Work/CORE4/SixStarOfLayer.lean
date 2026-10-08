import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple
import Submission.Work.CORE4.Case2Six9

namespace Work.CORE4

set_option linter.style.haveILetI false

/-- **Design-19 leaf S5**: (★) from S3–S4, i.e. `N_G(X) ≤ D.M` for `1 ≠ X ≤ D.F`.

Statement (verbatim, `Work.GW2.C19.SixStarOfLayerProp`): for `BenderCtx G`, `B`, `D` with
`Case2Pre B D`, `X ≠ ⊥`, `X ≤ D.F`, `B.t ∈ layerIn (N_G(X))` (S2),
`layerIn D.M ≤ layerIn (N_G(X))` (S3), `layerIn (N_G(X)) ≤ D.M` (S4):
`normalizer (X : Set G) ≤ D.M`.

Route: `E₀ := layerIn (N_G(X)) ≤ M ≤ N_G(E)` (S4 and `layerIn_le_normalizer`), so `E ⊴ E₀`; `E₀`
is quasisimple with `E := layerIn D.M` a normal quasisimple subgroup
(`Work.CORE4.layer_facts_proper_quasisimple` at `N_G(X)`, which needs `N_G(X) ≠ ⊤` — from
`X ≠ ⊥`, `X ≤ F ≤ M < ⊤` and simplicity), so
`Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple` at `K := E₀` gives `layerIn E₀ = E`;
applying it again with `E := E₀`, `K := E₀` gives `layerIn E₀ = E₀`.  Hence `E₀ = E`, and
`N_G(X) ≤ N_G(E₀) = N_G(E) = D.M` (`layerIn_le_normalizer` and the proved
`Case2Six9.normalizer_layerIn_eq_data`). -/
theorem SixStarOfLayer (I : Work.GW2.C4Inputs) : Work.GW2.C19.SixStarOfLayerProp I := by
  intro G _inst _fin hbc B D hpre X hX hXF ht hS3 hS4
  haveI : IsSimpleGroup G := hbc.simple
  -- `X ≤ D.M`: `X ≤ F ≤ B₀ ≤ U ⊓ M`
  have hXDM : X ≤ D.M := le_trans hXF (le_trans (D.F_le_UinfM B) inf_le_right)
  -- `N_G(X) ≠ ⊤`, else `X ⊴ G` and simplicity forces `X = ⊤`, against `X ≤ D.M < ⊤`
  have hKtop : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro htop
    have hXnorm : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hXnorm.eq_bot_or_eq_top with hb | htop'
    · exact hX hb
    · exact D.M_coatom.ne_top (top_le_iff.mp (htop' ▸ hXDM))
  -- `E₀ := E(N_G(X)) ≤ M < ⊤`
  have hE0top : Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) ≠ ⊤ :=
    fun h => D.M_coatom.ne_top (top_le_iff.mp (h ▸ hS4))
  -- `E := E(M)` is quasisimple (Bender §4, p. 224)
  have hEQ : Work.GW2.IsQuasisimple (Work.GW2.layerIn D.M) := by
    obtain ⟨E1, -, hlayer, hQ1, -, -⟩ :=
      Work.CORE4.layer_facts_proper_quasisimple I hbc D.M_coatom.ne_top D.t_mem
    rw [Work.GW2.layerIn, hlayer]
    exact Work.CORE4.isQuasisimple_map _ (Subgroup.subtype_injective D.M) hQ1
  -- `E₀` is quasisimple (same lemma at `N_G(X)`, which is proper)
  have hE0Q : Work.GW2.IsQuasisimple (Work.GW2.layerIn (Subgroup.normalizer (X : Set G))) := by
    obtain ⟨E1, -, hlayer, hQ1, -, -⟩ :=
      Work.CORE4.layer_facts_proper_quasisimple I hbc hKtop ht
    rw [Work.GW2.layerIn, hlayer]
    exact Work.CORE4.isQuasisimple_map _ (Subgroup.subtype_injective _) hQ1
  -- `E₀ ≤ M ≤ N_G(E)`, so `E ⊴ E₀` and the uniqueness of the normal quasisimple subgroup of the
  -- proper subgroup `E₀` gives `E(E₀) = E`
  have hA : Work.GW2.layerIn (Work.GW2.layerIn (Subgroup.normalizer (X : Set G))) =
      Work.GW2.layerIn D.M :=
    Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple I hbc hE0top hS3
      (le_trans hS4 (Work.CORE4.layerIn_le_normalizer D.M)) hEQ
  -- applying it again with `E := E₀` gives `E(E₀) = E₀`
  have hB : Work.GW2.layerIn (Work.GW2.layerIn (Subgroup.normalizer (X : Set G))) =
      Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) :=
    Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple I hbc hE0top le_rfl
      (le_trans (Work.CORE4.layerIn_le (Subgroup.normalizer (X : Set G)))
        (Work.CORE4.layerIn_le_normalizer (Subgroup.normalizer (X : Set G)))) hE0Q
  -- hence `E = E₀`
  have hEq : Work.GW2.layerIn D.M =
      Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) := hA.symm.trans hB
  -- and `N_G(E₀) = N_G(E) = M`
  have hN : Subgroup.normalizer
      (((Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) : Subgroup G)) : Set G) = D.M := by
    rw [← hEq]
    exact Work.CORE4.normalizer_layerIn_eq_data hbc D
  -- finally `N_G(X) ≤ N_G(E₀) = M`
  calc Subgroup.normalizer (X : Set G)
      ≤ Subgroup.normalizer
          (((Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) : Subgroup G)) : Set G) :=
        Work.CORE4.layerIn_le_normalizer (Subgroup.normalizer (X : Set G))
    _ = D.M := hN

end Work.CORE4
