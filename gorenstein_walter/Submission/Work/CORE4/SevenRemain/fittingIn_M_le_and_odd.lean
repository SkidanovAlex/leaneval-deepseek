import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.SevenRemain.fittingIn_le_centralizer_layerIn

namespace Work.CORE4.SevenRemain

/-! The second auxiliary fact used below (an involution centralizing a Sylow `2`-subgroup lies in
it) is kept *private* and inlined here as `sylow_mem_of_orderOf_eq_two_of_le_centralizer`; the
public version of the same statement is being proved at
`Submission/Work/CORE4/SevenRemain/mem_sylow_of_orderOf_eq_two_of_le_centralizer.lean`, and can be
used instead once it is available.

Scratch files of this development, left in place but to be ignored: `_childstub.lean` (a stub of
the two auxiliary lemmas, used to develop the proof below) and `_probe_mine.lean` (the import
probe for that stub); `_ax_mine.lean` is the `#print axioms` check for this module. -/

private theorem sylow_mem_of_orderOf_eq_two_of_le_centralizer {X : Type} [Group X] [Finite X]
    (P : Sylow 2 X) {x : X} (hx : orderOf x = 2)
    (hc : (P : Subgroup X) ≤ Subgroup.centralizer ({x} : Set X)) : x ∈ P := by
  by_contra hxP
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  have hxcen : x ∈ Subgroup.centralizer (((P : Subgroup X)) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hc ha) x (Set.mem_singleton x)).symm
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hxcen)
  let Q : Subgroup X := (P : Subgroup X) ⊔ Subgroup.zpowers x
  have hQp : IsPGroup 2 Q := P.isPGroup'.to_sup_of_normal_left' hzp hnorm
  have hmax : Q = (P : Subgroup X) := P.is_maximal' hQp le_sup_left
  have hxQ : x ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [hmax] at hxQ
  exact hxP hxQ

/-- **Bender 1981, §4: `F(M) ≤ H ⊓ M` and `F(M)` is odd.**

`E := layerIn D.M` satisfies `E ≅ PSL(2, q)` with `q ≥ 7` (`Case2Ctx.nine`), hence `E` is simple
non-abelian; `E ⊴ M` and `F(M) ⊴ M` give `[F(M), E] ≤ F(M) ⊓ E = 1` (a proper normal subgroup of
`E` is trivial, and `E ≤ F(M)` is impossible since `E` is not nilpotent), so
`F(M) ≤ C_M(E) ≤ C_M(t) = H ⊓ M`.

For the oddness: `O₂(M) ≤ S` (`S` is a Sylow 2-subgroup of `M` by `Case2PrePlus`, which is
`Work.CORE4.Case2PrePlusOfCtx`), `S ≤ E` (`Case2Ctx.nine`), so `[O₂(M), E] ≤ O₂(M) ⊓ E` is a
normal subgroup of `E` contained in a 2-group, whence `O₂(M) ≤ Z(E) = 1`.  As `F(M)` is nilpotent,
its 2-Sylow subgroup is characteristic in `F(M) ⊴ M`, hence normal in `M`, hence contained in
`O₂(M) = 1`. -/
theorem fittingIn_M_le_and_odd (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.fittingIn h.D.M ≤ B.H ⊓ h.D.M ∧
          ¬ 2 ∣ Nat.card ↥(Work.GW2.fittingIn h.D.M) := by
  intro G _ _ hbc B h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Part 1.  `E(M) = layerIn M` centralizes `F(M)` (`fittingIn_le_centralizer_layerIn`), and
  -- `t ∈ E(M)` (`Case2Data.t_mem`), so `F(M) ≤ C_G(t) = H`.
  have hFE : Work.GW2.fittingIn h.D.M ≤
      Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
    fittingIn_le_centralizer_layerIn h.D.M
  have hFH : Work.GW2.fittingIn h.D.M ≤ B.H := by
    intro x hx
    show x ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp (hFE hx) B.t h.D.t_mem
  refine ⟨le_inf hFH (Subgroup.map_subtype_le _), ?_⟩
  -- ## Part 2.  `F(M)` is odd.
  -- ### `Z(E(M))` has odd order, by `LayerCtx6` (§4: `E(M)` is quasisimple with `E/Z(E)` a
  -- group of Lie type in odd characteristic).
  have hOddC : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn h.D.M))) := by
    let h6 : Work.GW2.Case2Ctx6 B := ⟨h.D, h.pre, h.F_ti, h.F_cyclic⟩
    have hD : Work.GW2.DihOrCycSylow ↥h6.D.M := Work.CORE4.DihOrCycSub hbc.sylow h6.D.M
    exact (Work.CORE4.LayerCtx6 I hbc h6 hD).2.1
  -- ### Hence `F(M)` has no element of order `2`.
  -- An involution `g ∈ F(M)` centralizes `E(M) ⊇ S` (`S` is a Sylow `2`-subgroup of `G` with
  -- `S ≤ E(M)`, §4 (9)), so `g ∈ S ⊆ E(M)` by
  -- `sylow_mem_of_orderOf_eq_two_of_le_centralizer`; but `g ∈ E(M) ∩ C_G(E(M)) = Z(E(M))`
  -- would force `2 ∣ |Z(E(M))|`.
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Work.GW2.fittingIn h.D.M)) 2 h2
  have hord : orderOf (g : G) = 2 := (Subgroup.orderOf_coe g).trans hg
  have hcomm : ∀ y ∈ Work.GW2.layerIn h.D.M, y * (g : G) = (g : G) * y :=
    fun y hy => Subgroup.mem_centralizer_iff.mp (hFE g.2) y hy
  have hxnotE : (g : G) ∉ Work.GW2.layerIn h.D.M := by
    intro hxE
    have hcen : (⟨(g : G), hxE⟩ : ↥(Work.GW2.layerIn h.D.M)) ∈
        Subgroup.center ↥(Work.GW2.layerIn h.D.M) := by
      rw [Subgroup.mem_center_iff]
      intro e
      apply Subtype.ext
      show (e : G) * (g : G) = (g : G) * (e : G)
      exact hcomm (e : G) e.2
    have hdvd : orderOf (⟨(g : G), hxE⟩ : ↥(Work.GW2.layerIn h.D.M)) ∣
        Nat.card ↥(Subgroup.center ↥(Work.GW2.layerIn h.D.M)) :=
      Subgroup.orderOf_dvd_natCard _ hcen
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hOddC) (even_iff_two_dvd.mpr hdvd)
  have hcS : (B.S : Subgroup G) ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hcomm s (Work.CORE4.S_le_layerIn h hs)).symm
  exact hxnotE (Work.CORE4.S_le_layerIn h
    (sylow_mem_of_orderOf_eq_two_of_le_centralizer (B.S) hord hcS))

end Work.CORE4.SevenRemain
