/-
# BMAX — Bender 1970, 1.6 in the `D`-group form (`Work.BMAX.Bender16DGroup`)

Target:

`theorem Work.BMAX.Bender16DGroup : Work.GW2.Bender16Prop`

unfolded (`G` is a group in the lowest universe, as in `Work.GW2.Bender16Prop`):

`∀ (T : LocalToolkit) (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ A B,
  DihOrCycSylow A → IsDGroup A → DihOrCycSylow B → IsDGroup B → IsCoatom A → IsCoatom B → A ≠ B →
  fstarIn A ≤ B → fstarIn B ≤ A → ∃ p, p.Prime ∧ IsPGroup p (fstarIn A) ∧ IsPGroup p (fstarIn B)`.

## Structure of the proof (Bender 1970, 1.6)

Write `F_A := F(A)`, `L_A := layer(A)`, `F*_A := F*(A) = F_A · L_A`; likewise for `B`.

* **Step 1 (`layerIn A = layerIn B = ⊥`)**, proved here (`b16d_layerIn_eq_bot`).  For a normal
  quasisimple `E ≤ ↥A` and a normal quasisimple `F ≤ ↥B` the subgroups `E.map A.subtype` and
  `F.map B.subtype` normalise each other (as `E.map A.subtype ≤ F*(A) ≤ B`,
  `F.map B.subtype ≤ F*(B) ≤ A`) and are distinct (equal would make the common subgroup normal
  in `⟨A,B⟩ = ⊤`, hence in the simple `G`, hence `⊤`, against `≤ A ≠ ⊤`), so they commute;
  `[E.map A.subtype, F(B)] = 1` similarly.  Hence `L_A` centralises `F*(B) = F(B)·L_B`; since
  `L_A ≤ F*(A) ≤ B` and `B` is a `D`-group, the self-centralisation `C_B(F*(B)) ≤ F*(B)`
  (`T.fstar`) gives `L_A ≤ F*(B)`; as `L_A` also centralises `F*(B)` it lies in the centre of
  `F*(B)`, which is commutative, so `L_A = ⊥`.

* **Step 2 (the `D`-group case)**, proved as `Work.BMAX.B16Core` (`B16Core.lean`).  With
  `F*_A = F_A`, `F*_B = F_B` nilpotent, Bender's argument applies: for `p ∈ π(F_A)`, a fixed
  prime below `O_p(A) ≠ ⊥`, the generalized Fitting subgroups of `A` and of `B` are `p`-groups.

The final assembly (`Bender16Prop_of_crux`) runs the two steps and disposes of the degenerate
case `F(A) = ⊥` by symmetry.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.Bender16
import Submission.Work.BMAX.B16Aux
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.commutator_eq_bot_of_isQuasisimple_of_isQuasisimple
import Submission.Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf
import Submission.Work.BMAX.B16Core

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

/-! ## 0. Two coatomic subgroups generate the group -/

theorem b16d_sup_eq_top {G : Type} [Group G] {A B : Subgroup G} (hA : IsCoatom A)
    (hB : IsCoatom B) (hne : A ≠ B) : A ⊔ B = ⊤ := by
  by_contra h
  have hle : A ⊔ B = A := by
    rcases lt_or_eq_of_le (le_sup_left : A ≤ A ⊔ B) with hlt | heq
    · exact absurd (hA.lt_iff.mp hlt) h
    · exact heq.symm
  have hBA : B ≤ A := le_trans le_sup_right (le_of_eq hle)
  have hlt : B < A := lt_of_le_of_ne hBA (Ne.symm hne)
  exact hA.ne_top (hB.lt_iff.mp hlt)

/-! ## 1. `F*` self-centralisation in the ambient-group form -/

/-- The toolkit's `FStarProp`, transported to the ambient-group form
`C_G(F*(B)) ∩ B ≤ F*(B)` for a `D`-group `B`. -/
theorem centralizer_fstarIn_inf_le {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) {B : Subgroup G}
    (hDB : Work.GW2.DihOrCycSylow B) (hDGB : Work.GW2.IsDGroup B) :
    Subgroup.centralizer (Work.GW2.fstarIn B : Set G) ⊓ B ≤ Work.GW2.fstarIn B := by
  intro x hx
  obtain ⟨hcen, hxB⟩ := Subgroup.mem_inf.mp hx
  have hMem : (⟨x, hxB⟩ : ↥B) ∈
      Subgroup.centralizer ((Work.GW2.fstar ↥B : Subgroup ↥B) : Set ↥B) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ Work.GW2.fstarIn B := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hcomm : (y : G) * x = x * (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hcen) (y : G) hy'
    exact Subtype.ext (by simpa using hcomm)
  have h2 : (⟨x, hxB⟩ : ↥B) ∈ Work.GW2.fstar ↥B := T.fstar ↥B T.ft hDB hDGB hMem
  exact Subgroup.mem_map.mpr ⟨⟨x, hxB⟩, h2, rfl⟩

/-! ## 2. The cross-commutation lemmas (Bender 1.6, step 1) -/

/-- **`⁅layerIn A, fittingIn B⁆ = ⊥`** (and symmetrically), under the pair hypotheses. -/
theorem b16d_layerIn_commutes_fittingIn_cross {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B)
    (hne : A ≠ B) (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A) :
    ⁅Work.GW2.layerIn A, Work.GW2.fittingIn B⁆ = ⊥ ∧
    ⁅Work.GW2.layerIn B, Work.GW2.fittingIn A⁆ = ⊥ := by
  have hcross : ∀ {X Y : Subgroup G}, Work.GW2.fstarIn X ≤ Y → Work.GW2.fstarIn Y ≤ X →
      ⁅Work.GW2.layerIn X, Work.GW2.fittingIn Y⁆ = ⊥ := by
    intro X Y hXY hYX
    refine b16_commutator_layerIn_eq_bot (A := X) (K := Work.GW2.fittingIn Y) ?_
    intro E hEn hEq
    have hEG : E.map X.subtype ≤ Work.GW2.layerIn X := by
      rw [Work.GW2.layerIn, Work.GW2.layer]
      exact Subgroup.map_mono (le_sSup (show E ∈
        {F : Subgroup ↥X | F.Normal ∧ Work.GW2.IsQuasisimple F} from ⟨hEn, hEq⟩))
    have hQq : Work.GW2.IsQuasisimple (E.map X.subtype) :=
      b16_isQuasisimple_map _ X.subtype_injective hEq
    have hQle : E.map X.subtype ≤ Y :=
      le_trans hEG (le_trans (Work.GW2.layerIn_le_fstarIn X) hXY)
    have hNle : Work.GW2.fittingIn Y ≤ X :=
      le_trans (Work.GW2.fittingIn_le_fstarIn Y) hYX
    have hQN : E.map X.subtype ≤ Subgroup.normalizer (Work.GW2.fittingIn Y : Set G) :=
      le_trans hQle (le_normalizer_fittingIn Y)
    have hNQ : Work.GW2.fittingIn Y ≤
        Subgroup.normalizer ((E.map X.subtype : Subgroup G) : Set G) :=
      le_trans hNle (le_normalizer_map_subtype_of_normal (A := X) hEn)
    haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn Y) := isNilpotent_fittingIn Y
    exact b16_commutator_eq_bot_of_isQuasisimple_of_nilpotent_cross hQq hQN hNQ
  exact ⟨hcross hAB hBA, hcross hBA hAB⟩

/-- **`⁅layerIn A, layerIn B⁆ = ⊥`** under the pair hypotheses. -/
theorem b16d_layerIn_layerIn_commute {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B)
    (hne : A ≠ B) (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A) :
    ⁅Work.GW2.layerIn A, Work.GW2.layerIn B⁆ = ⊥ := by
  refine b16_commutator_layerIn_layerIn_eq_bot (A := A) (B := B) ?_
  intro E F hEn hFn hEq hFq
  have hEG : E.map A.subtype ≤ Work.GW2.layerIn A := by
    rw [Work.GW2.layerIn, Work.GW2.layer]
    exact Subgroup.map_mono (le_sSup (show E ∈
      {F : Subgroup ↥A | F.Normal ∧ Work.GW2.IsQuasisimple F} from ⟨hEn, hEq⟩))
  have hFG : F.map B.subtype ≤ Work.GW2.layerIn B := by
    rw [Work.GW2.layerIn, Work.GW2.layer]
    exact Subgroup.map_mono (le_sSup (show F ∈
      {F : Subgroup ↥B | F.Normal ∧ Work.GW2.IsQuasisimple F} from ⟨hFn, hFq⟩))
  have hQq : Work.GW2.IsQuasisimple (E.map A.subtype) :=
    b16_isQuasisimple_map _ A.subtype_injective hEq
  have hPq : Work.GW2.IsQuasisimple (F.map B.subtype) :=
    b16_isQuasisimple_map _ B.subtype_injective hFq
  have hQleB : E.map A.subtype ≤ B := le_trans hEG (le_trans (Work.GW2.layerIn_le_fstarIn A) hAB)
  have hPleA : F.map B.subtype ≤ A := le_trans hFG (le_trans (Work.GW2.layerIn_le_fstarIn B) hBA)
  have hQP : E.map A.subtype ≤ Subgroup.normalizer ((F.map B.subtype : Subgroup G) : Set G) :=
    le_trans hQleB (le_normalizer_map_subtype_of_normal (A := B) hFn)
  have hPQ : F.map B.subtype ≤ Subgroup.normalizer ((E.map A.subtype : Subgroup G) : Set G) :=
    le_trans hPleA (le_normalizer_map_subtype_of_normal (A := A) hEn)
  have hne' : (E.map A.subtype : Subgroup G) ≠ F.map B.subtype := by
    intro heq
    have hQB : B ≤ Subgroup.normalizer ((E.map A.subtype : Subgroup G) : Set G) :=
      heq.symm ▸ le_normalizer_map_subtype_of_normal (A := B) hFn
    have hQA : A ≤ Subgroup.normalizer ((E.map A.subtype : Subgroup G) : Set G) :=
      le_normalizer_map_subtype_of_normal (A := A) hEn
    have htop : A ⊔ B ≤ Subgroup.normalizer ((E.map A.subtype : Subgroup G) : Set G) :=
      sup_le hQA hQB
    rw [b16d_sup_eq_top hA hB hne] at htop
    have hnorm : (E.map A.subtype : Subgroup G).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
    haveI := hnorm
    rcases hG.eq_bot_or_eq_top_of_normal (E.map A.subtype) with h | h
    · exact QuasiComm.isQuasisimple_ne_bot hQq h
    · exact hA.ne_top (top_le_iff.mp (h ▸ le_trans hEG (Work.GW2.layerIn_le_self A)))
  exact commutator_eq_bot_of_isQuasisimple_of_isQuasisimple hQq hPq hQP hPQ hne'

/-! ## 3. Step 1: the layers vanish -/

/-- **Step 1.**  `layerIn A = ⊥` under the Bender-1.6 pair hypotheses, `B` a `D`-group (so that
`C_B(F*(B)) ≤ F*(B)` is available). -/
theorem b16d_layerIn_eq_bot_left {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G)
    {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hDB : Work.GW2.DihOrCycSylow B) (hDGB : Work.GW2.IsDGroup B)
    (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A) :
    Work.GW2.layerIn A = ⊥ := by
  have hc1 : ⁅Work.GW2.layerIn A, Work.GW2.fittingIn B⁆ = ⊥ :=
    (b16d_layerIn_commutes_fittingIn_cross hG hA hB hne hAB hBA).1
  have hc2 : ⁅Work.GW2.layerIn A, Work.GW2.layerIn B⁆ = ⊥ :=
    b16d_layerIn_layerIn_commute hG hA hB hne hAB hBA
  have hcen : Work.GW2.layerIn A ≤ Subgroup.centralizer (Work.GW2.fstarIn B : Set G) := by
    rw [Work.GW2.fstarIn_eq_sup, Subgroup.centralizer_sup]
    exact le_inf (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc2)
  have hBle : Work.GW2.layerIn A ≤ B := le_trans (Work.GW2.layerIn_le_fstarIn A) hAB
  have hfs : Work.GW2.layerIn A ≤ Work.GW2.fstarIn B :=
    le_trans (le_inf hcen hBle) (centralizer_fstarIn_inf_le T hDB hDGB)
  -- the layer of `A` lies in the centre of `F*(B)`, which is commutative
  set Z : Subgroup G :=
    (Subgroup.center ↥(Work.GW2.fstarIn B)).map (Work.GW2.fstarIn B).subtype with hZdef
  have hZcomm : IsMulCommutative ↥Z := by
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
    obtain ⟨cx, hcx, hxv⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨cy, hcy, hyv⟩ := Subgroup.mem_map.mp y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [show (x : G) = (cx : G) from hxv.symm, show (y : G) = (cy : G) from hyv.symm]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcy) cx)
  have hleZ : Work.GW2.layerIn A ≤ Z := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hfs hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by
      have hy : (y : G) ∈ Work.GW2.fstarIn B := y.2
      have hcomm : (y : G) * x = x * (y : G) :=
        (Subgroup.mem_centralizer_iff.mp (hcen hx)) (y : G) hy
      simpa using hcomm)
  exact b16_layerIn_eq_bot_of_le_isMulCommutative hZcomm hleZ

/-- **Step 1, both sides.** -/
theorem b16d_layerIn_eq_bot {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G)
    {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hDA : Work.GW2.DihOrCycSylow A) (hDGA : Work.GW2.IsDGroup A)
    (hDB : Work.GW2.DihOrCycSylow B) (hDGB : Work.GW2.IsDGroup B)
    (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A) :
    Work.GW2.layerIn A = ⊥ ∧ Work.GW2.layerIn B = ⊥ :=
  ⟨b16d_layerIn_eq_bot_left T hG hA hB hne hDB hDGB hAB hBA,
   b16d_layerIn_eq_bot_left (A := B) (B := A) T hG hB hA (Ne.symm hne) hDA hDGA hBA hAB⟩

/-- `F*(K) = F(K)` once the layer of `K` is trivial. -/
theorem b16d_fstarIn_eq_fittingIn {G : Type} [Group G] {K : Subgroup G}
    (hL : Work.GW2.layerIn K = ⊥) : Work.GW2.fstarIn K = Work.GW2.fittingIn K := by
  rw [Work.GW2.fstarIn_eq_sup K, hL, sup_bot_eq]

/-! ## 4. A nontrivial Fitting subgroup has a nontrivial `p`-core -/

/-- If `F(K) ≠ ⊥` then `O_p(K) ≠ ⊥` for some prime `p`. -/
theorem exists_pCoreIn_ne_bot_of_fittingIn_ne_bot {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (h : Work.GW2.fittingIn K ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Work.GW2.pCoreIn p K ≠ ⊥ := by
  have hcard : Nat.card ↥(Work.GW2.fittingIn K) ≠ 1 := fun h1 =>
    h (Subgroup.card_eq_one.mp h1)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  refine ⟨p, hp, fun hbot => ?_⟩
  have hmem : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn K) := by
    rw [Work.GW2.primesOf]
    exact Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩
  exact ((pCoreIn_eq_bot_iff_not_mem_primesOf K p hp).mp hbot) hmem

/-! ## 5. The assembly -/

/-- **Bender 1970, 1.6, assembled from its `D`-group core.**

`crux` is the one irreducible ingredient: under the pair hypotheses with both layers trivial and
`p ∈ π(F(A))`, the generalized Fitting subgroups of `A` and `B` are `p`-groups. -/
theorem Bender16Prop_of_crux
    (crux : ∀ {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G)
      {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
      (hDA : Work.GW2.DihOrCycSylow A) (hDGA : Work.GW2.IsDGroup A)
      (hDB : Work.GW2.DihOrCycSylow B) (hDGB : Work.GW2.IsDGroup B)
      (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A)
      (hLA : Work.GW2.layerIn A = ⊥) (hLB : Work.GW2.layerIn B = ⊥)
      (p : ℕ) (hp : p.Prime) (hpA : Work.GW2.pCoreIn p A ≠ ⊥),
      IsPGroup p ↥(Work.GW2.fstarIn A) ∧ IsPGroup p ↥(Work.GW2.fstarIn B)) :
    Work.GW2.Bender16Prop := by
  intro T G _ _ hG A B hDA hDGA hDB hDGB hA hB hne hAB hBA
  obtain ⟨hLA, hLB⟩ := b16d_layerIn_eq_bot T hG hA hB hne hDA hDGA hDB hDGB hAB hBA
  have hfA : Work.GW2.fstarIn A = Work.GW2.fittingIn A := b16d_fstarIn_eq_fittingIn hLA
  have hfB : Work.GW2.fstarIn B = Work.GW2.fittingIn B := b16d_fstarIn_eq_fittingIn hLB
  by_cases hFA : Work.GW2.fittingIn A = ⊥
  · by_cases hFB : Work.GW2.fittingIn B = ⊥
    · refine ⟨2, Nat.prime_two, ?_, ?_⟩
      · rw [hfA, hFA]; exact IsPGroup.of_bot
      · rw [hfB, hFB]; exact IsPGroup.of_bot
    · obtain ⟨p, hp, hpB⟩ := exists_pCoreIn_ne_bot_of_fittingIn_ne_bot hFB
      obtain ⟨hpgB, -⟩ :=
        crux T hG hB hA (Ne.symm hne) hDB hDGB hDA hDGA hBA hAB hLB hLA p hp hpB
      refine ⟨p, hp, ?_, ?_⟩
      · rw [hfA, hFA]; exact IsPGroup.of_bot
      · exact hpgB
  · obtain ⟨p, hp, hpA⟩ := exists_pCoreIn_ne_bot_of_fittingIn_ne_bot hFA
    obtain ⟨hpgA, hpgB⟩ :=
      crux T hG hA hB hne hDA hDGA hDB hDGB hAB hBA hLA hLB p hp hpA
    refine ⟨p, hp, ?_, ?_⟩
    · exact hpgA
    · exact hpgB

/-- The delegated `D`-group core, in the exact shape consumed by `Bender16Prop_of_crux`. -/
theorem b16d_crux {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hG : IsSimpleGroup G) {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B)
    (hne : A ≠ B) (hDA : Work.GW2.DihOrCycSylow A) (hDGA : Work.GW2.IsDGroup A)
    (hDB : Work.GW2.DihOrCycSylow B) (hDGB : Work.GW2.IsDGroup B)
    (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A)
    (hLA : Work.GW2.layerIn A = ⊥) (hLB : Work.GW2.layerIn B = ⊥)
    (p : ℕ) (hp : p.Prime) (hpA : Work.GW2.pCoreIn p A ≠ ⊥) :
    IsPGroup p ↥(Work.GW2.fstarIn A) ∧ IsPGroup p ↥(Work.GW2.fstarIn B) :=
  B16Core T hG hA hB hne hDA hDGA hDB hDGB hAB hBA hLA hLB p hp hpA

/-- **Bender 1970, 1.6** in the `D`-group form: the goal of this file. -/
theorem Bender16DGroup : Work.GW2.Bender16Prop :=
  Bender16Prop_of_crux b16d_crux

end Work.BMAX
