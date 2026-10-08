import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.API
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic
import Submission.Work.CORE4.TwoResidualPerfect.twoResidual_eq_top_of_isPerfect
import Submission.Work.CORE4.FittingMonotone.fittingIn_le_fittingIn_of_le_normalizer
import Submission.Work.CORE4.SylowNotCyclic.sylow_not_isCyclic_of_le_quasisimple

namespace Work.CORE4

open Work.GW2 Subgroup

/-! ## Helper lemmas for leaf S2

The elementary pieces of the argument, in area CORE4's own vocabulary. -/

/-- `K ≤ N_G(O(K))`: the odd core of `K` (realized in the ambient group) is normal in `K`. -/
theorem oddCoreIn_le_normalizer {G : Type*} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.oddCoreIn K : Subgroup G) : Set G) := by
  have hnorm : (Work.GW2.oddCore K).Normal := Work.GW2.oddCore_normal K
  rw [Subgroup.le_normalizer_iff]
  intro m hm x hx
  rw [Work.GW2.oddCoreIn] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, Subgroup.Normal.conj_mem hnorm y hy ⟨m, hm⟩, by simp⟩

/-- **Universal property of the relative `2`-residual**: `O²(K) ≤ N` iff every element of `K` of
odd order lies in `N`. -/
theorem twoResidualIn_le_iff {G : Type*} [Group G] {K N : Subgroup G} :
    Work.GW2.twoResidualIn K ≤ N ↔ ∀ k : ↥K, Odd (orderOf k) → (k : G) ∈ N := by
  constructor
  · intro h k hk
    exact h ⟨k, Subgroup.subset_closure hk, rfl⟩
  · intro h
    rw [Work.GW2.twoResidualIn, Work.GW2.twoResidual, Subgroup.map_le_iff_le_comap,
      Subgroup.closure_le]
    intro z hz
    exact h z hz

/-- `O²(-)` is monotone: `K ≤ M → O²(K) ≤ O²(M)`. -/
theorem twoResidualIn_mono {G : Type*} [Group G] {K M : Subgroup G} (h : K ≤ M) :
    Work.GW2.twoResidualIn K ≤ Work.GW2.twoResidualIn M := by
  rw [Work.GW2.twoResidualIn, Work.GW2.twoResidual, Work.GW2.twoResidualIn, Work.GW2.twoResidual,
    Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  intro z hz
  have hzM : Odd (orderOf (⟨(z : G), h z.2⟩ : ↥M)) := by
    have hlin : orderOf (⟨(z : G), h z.2⟩ : ↥M) = orderOf z := by
      rw [← Subgroup.orderOf_coe (⟨(z : G), h z.2⟩ : ↥M), ← Subgroup.orderOf_coe z]
    rw [hlin]; exact hz
  exact Subgroup.mem_map.mpr ⟨⟨(z : G), h z.2⟩, Subgroup.subset_closure hzM, rfl⟩

/-- A perfect subgroup `M ≤ G` is contained in its own `2`-residual realized in `G`. -/
theorem le_twoResidualIn_self_of_perfect {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hperf : ⁅M, M⁆ = M) : M ≤ Work.GW2.twoResidualIn M := by
  haveI : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hperf
  have htop : Work.GW2.twoResidual ↥M = ⊤ :=
    Work.CORE4.TwoResidualPerfect.twoResidual_eq_top_of_isPerfect
  rw [Work.GW2.twoResidualIn, htop, Subgroup.map_top, Subgroup.range_subtype]

/-- **A quasisimple subgroup of a solvable group is impossible**: this is the contradiction at the
end of leaf S2. -/
theorem not_isSolvable_of_le_quasisimple {G : Type*} [Group G] {E M : Subgroup G}
    (hE : Work.GW2.IsQuasisimple E) (hEM : E ≤ M) (hsol : Group.IsSolvable ↥M) : False := by
  haveI : Group.IsSolvable ↥M := hsol
  haveI hsolE : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hEM)
      (Subgroup.inclusion_injective hEM)
  haveI hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE.1
  haveI hnt : Nontrivial ↥E := by
    by_contra hcon
    haveI : Subsingleton ↥E := not_nontrivial_iff_subsingleton.mp hcon
    haveI : Nontrivial (↥E ⧸ Subgroup.center ↥E) := hE.2.toNontrivial
    exact not_subsingleton (↥E ⧸ Subgroup.center ↥E) inferInstance
  exact Group.IsPerfect.not_isSolvable ↥E inferInstance

/-- **`E(M) = layerIn D.M` is quasisimple** for the §4 configuration, with no hypotheses beyond
`BenderCtx` and the data `D` (the proof of `Work.CORE4.layer_facts_proper_quasisimple` uses the
coatom only through `M ≠ ⊤`, and `D.t_mem` provides `t ∈ layerIn D.M`). -/
theorem isQuasisimple_layerIn_of_case2 {G : Type} [Group G] [Finite G]
    (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} (D : Work.GW2.Case2Data B) :
    Work.GW2.IsQuasisimple (Work.GW2.layerIn D.M) := by
  obtain ⟨E1, -, hlay, hE1q, -, -⟩ :=
    layer_facts_proper_quasisimple I hbc (B := B) (M := D.M) D.M_coatom.ne_top D.t_mem
  change Work.GW2.IsQuasisimple ((Work.GW2.layer ↥D.M).map D.M.subtype)
  rw [hlay]
  exact isQuasisimple_map D.M.subtype D.M.subtype_injective hE1q

/-- **Design-19 leaf S2**: `t ∈ E(N_G(X))` for `1 ≠ X ≤ F`, via Bender's Lemma 2.7 applied at
`M₀ := N_G(X)`.

Statement (verbatim): `SixTInLayerNProp I` = for `BenderCtx G`, `B`, `D` with `Case2Pre B D`,
`¬ layerIn D.M ≤ B.Hhat` (leaf S1), and `X ≠ ⊥`, `X ≤ D.F`: `B.t ∈ layerIn (N_G(X))`.

Route (contrapositive of `I.lem27 : Lemma27Prop`, applied with `M := N_G(X)` and
`I.toolkit.ft`):
* `N_G(X) ≠ ⊤`: otherwise `X ⊴ G` and simplicity forces `X = ⊤`, but `X ≤ D.F ≤ D.M < ⊤`;
* `BRel B.Hhat (N_G(X))` with witness `X`: `X ≤ F(U) ≤ F(Ĥ)` (from `D.F ≤ F(U)` and
  `F(U) ≤ F(Ĥ)`, the latter being `fittingIn_le_fittingIn_of_le_normalizer` applied to
  `U = O(Ĥ) ⊴ Ĥ`, `I.thm26`), and `N_G(X) ⊓ F*(Ĥ) ≤ N_G(X)`;
* `¬ N_G(X) ≤ B.Hhat`: `E = layerIn D.M ≤ C_G(F) ≤ C_G(X) ≤ N_G(X)` (`Case2Pre.F_cent`) and
  `E ≰ Ĥ` (S1);
* `t ∈ N_G(X)`: `t ∈ E ≤ C_G(X)`;
* Sylow 2-subgroups of `N_G(X)` are not cyclic
  (`Work.CORE4.SylowNotCyclic.sylow_not_isCyclic_of_le_quasisimple` for the quasisimple
  `E ≤ N_G(X)`);
* third disjunct: `t ∈ E = O²(E) ≤ O²(N_G(X))` (`E` perfect,
  `Work.CORE4.le_twoResidualIn_self_of_perfect` and `Work.CORE4.twoResidualIn_mono`).
Then `IsSolvable (N_G(X))` contradicts the quasisimple `E ≤ N_G(X)` via
`Work.CORE4.not_isSolvable_of_le_quasisimple`. -/
theorem SixTInLayerN (I : Work.GW2.C4Inputs) : Work.GW2.C19.SixTInLayerNProp I := by
  intro G _ _ hbc B D hpre hEhat X hX hXF
  classical
  haveI : IsSimpleGroup G := hbc.simple
  set M : Subgroup G := Subgroup.normalizer (X : Set G) with hMdef
  set E : Subgroup G := Work.GW2.layerIn D.M with hEdef
  have hEqs : Work.GW2.IsQuasisimple E := isQuasisimple_layerIn_of_case2 I hbc D
  have hEperf : ⁅E, E⁆ = E := hEqs.1
  have htE : B.t ∈ E := by rw [hEdef]; exact D.t_mem
  -- `E ≤ C_G(X) ≤ N_G(X) = M`
  have hEcen : E ≤ Subgroup.centralizer (X : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (Case2Pre.F_cent B D hpre (hXF hx)) e he).symm
  have hEM : E ≤ M := by
    rw [hMdef]
    exact le_trans hEcen (Subgroup.centralizer_le_normalizer (X : Set G))
  have htM : B.t ∈ M := hEM htE
  -- `¬ N_G(X) ≤ Ĥ`
  have hnotMle : ¬ M ≤ B.Hhat := fun hle => hEhat (le_trans hEM hle)
  -- `N_G(X) ≠ ⊤`
  have hMtop : M ≠ ⊤ := by
    intro htop
    have hnorm : X.Normal := by
      refine Subgroup.normalizer_eq_top_iff.mp ?_
      rw [← hMdef]; exact htop
    have hXtop : X = ⊤ := by
      rcases hnorm.eq_bot_or_eq_top with h | h
      · exact absurd h hX
      · exact h
    have hXDM : X ≤ D.M := le_trans hXF (le_trans (D.F_le_UinfM B) inf_le_right)
    exact D.M_coatom.ne_top (top_le_iff.mp (hXtop ▸ hXDM))
  -- `BRel B.Hhat M` with witness `X`: `X ≤ F(Ĥ)` via `U = O(Ĥ) ⊴ Ĥ` (`I.thm26`)
  have h26 := I.thm26 G I.toolkit.ft hbc B
  have hUle : B.U ≤ B.Hhat := by
    rw [← h26.1]; exact Subgroup.map_subtype_le (Work.GW2.oddCore B.Hhat)
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := oddCoreIn_le_normalizer B.Hhat
    rwa [h26.1] at h
  have hXfitH : X ≤ Work.GW2.fittingIn B.Hhat :=
    le_trans (le_trans hXF (D.F_le_fitting B))
      (Work.CORE4.FittingMonotone.fittingIn_le_fittingIn_of_le_normalizer hUle hUnorm)
  have hBRel : Work.GW2.BRel B.Hhat M := by
    refine ⟨X, hXfitH, ?_⟩
    rw [hMdef]; exact inf_le_left
  -- Sylow 2-subgroups of `M` are not cyclic
  have hsyl : ∀ P : Sylow 2 ↥M, ¬ IsCyclic ↥(P : Subgroup ↥M) :=
    Work.CORE4.SylowNotCyclic.sylow_not_isCyclic_of_le_quasisimple hEqs hEM
  -- third disjunct: `t ∈ O²(M)`
  have hres : B.t ∈ Work.GW2.twoResidualIn M := by
    have h1 : E ≤ Work.GW2.twoResidualIn E := le_twoResidualIn_self_of_perfect hEperf
    have h2 : Work.GW2.twoResidualIn E ≤ Work.GW2.twoResidualIn M :=
      twoResidualIn_mono hEM
    exact h2 (h1 htE)
  -- Lemma 2.7 at `M` gives `M` solvable, contradicting the quasisimple `E ≤ M`
  by_contra htnot
  have hsol : Group.IsSolvable ↥M :=
    (I.lem27 G I.toolkit.ft hbc B M hMtop hBRel hnotMle htM htnot hsyl
      (Or.inr (Or.inr hres))).2.2
  exact not_isSolvable_of_le_quasisimple hEqs hEM hsol

end Work.CORE4
