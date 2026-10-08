import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.InvCountH
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.NormalizerPcoreEqHhat

namespace Work.CORE3

open Subgroup

/-- A minimal counterexample has `|G| ≠ 2`: its Sylow `2`-subgroup `S` is dihedral of order
`2n ≥ 4`, so `G` has at least `4` elements. -/
private lemma card_G_ne_two {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty (((B.S : Subgroup G)) ≃* DihedralGroup n)) :
    Nat.card G ≠ 2 := by
  obtain ⟨e⟩ := hdih
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hle : Nat.card (B.S : Subgroup G) ≤ Nat.card G := Subgroup.card_le_card_group _
  rw [hcardS] at hle
  omega

/-- A simple group of order `≠ 2` has no normal subgroup of index `2`. -/
private lemma no_normal_index_two {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : Nat.card G ≠ 2) : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hIdx
  have hbot : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot] at hIdx
    exact hcard hIdx
  have htop : N ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hIdx
    omega
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple N hN with h | h
  · exact hbot h
  · exact htop h

/-- Bender 1981 §3, subcase `V = O₂(Ĥ)` of type `(2,2)`, the `V`-part of the centralizer
count: for every involution `s ∈ V = O₂(Ĥ)`, the involutions of `Ĥ` commuting with `s` number
`3 + 2|K|`.

Mathematical route.  `V` is a four-group (`D.four`) contained in `Ĥ` and normal in `Ĥ`
(`NormalizerPcoreEqHhat`), with `t ∈ V`.  The three non-identity elements of `V` are conjugate
under `N_G(V) = Ĥ` (`LocalToolkit.fus`, the four-group fusion of the dihedral Sylow theorem),
so conjugation by a suitable `g ∈ Ĥ` gives a bijection between the involutions of `Ĥ`
commuting with `t` and those commuting with `s`.  For `t` the set is exactly the involutions of
`B.H = C_G(t)` (since `B.H ≤ Ĥ`), whose number is `3 + 2|K|` by `InvCountH`. -/
theorem CommutingInvolsVsharp (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ s : G, s ∈ Work.GW2.pCoreIn 2 B.Hhat → orderOf s = 2 →
      (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K := by
  intro s hsV hs2
  classical
  -- The count for `H = C_G(t)`.
  have hInvH : (Work.GW2.involutionSet B.H).ncard = 3 + 2 * Nat.card D.K :=
    InvCountH I h B h1 D
  -- Structure: `t ∈ V = O₂(Ĥ)`.
  obtain ⟨hOC, hSC, hdisj⟩ := I.h26 G I.T.ft h B
  have hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) := D.four
  have htS : B.t ∈ (B.S : Subgroup G) := Work.CORE2A.bSetup_t_mem_S B
  have hUleH : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have htV : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    rw [← hSC]
    refine ⟨htS, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hUleH hy) B.t (Set.mem_singleton B.t)).symm
  have htne : B.t ≠ 1 := Work.CORE2A.bSetup_t_ne_one B
  have hsne : s ≠ 1 := by
    intro hs
    rw [hs, orderOf_one] at hs2
    norm_num at hs2
  -- ## The conjugation by `g ∈ Ĥ` with `g t g⁻¹ = s`.
  have hconj : (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({B.t} : Set G)).ncard
      = (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard := by
    obtain ⟨n2, hn2, hdih⟩ := SylowDihedral G h B
    have hNoIdx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
      no_normal_index_two h.simple (card_G_ne_two B n2 hn2 hdih)
    have hfus := (I.T.fus G B.S n2 hn2 hdih hNoIdx).2
    obtain ⟨g, hgN, hgt⟩ := hfus (Work.GW2.pCoreIn 2 B.Hhat) hV4 B.t htV s hsV htne hsne
    have hgH : g ∈ B.Hhat := by
      rw [← NormalizerPcoreEqHhat G h B hV4]
      exact hgN
    have hconj_g : ∀ a : G, g * (g⁻¹ * a * g) * g⁻¹ = a := by intro a; group
    refine Set.ncard_congr (fun x _ => g * x * g⁻¹) ?_ ?_ ?_
    · -- the image lands in the `s`-set
      rintro x ⟨⟨hxH, hxo⟩, hxC⟩
      have hxt : B.t * x = x * B.t := hxC B.t (Set.mem_singleton B.t)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact B.Hhat.mul_mem (B.Hhat.mul_mem hgH hxH) (B.Hhat.inv_mem hgH)
      · rw [show g * x * g⁻¹ = (MulAut.conj g) x by rw [MulAut.conj_apply]]
        exact (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hxo
      · refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        calc s * (g * x * g⁻¹) = (g * B.t * g⁻¹) * (g * x * g⁻¹) := by rw [hgt]
          _ = g * (B.t * x) * g⁻¹ := by group
          _ = g * (x * B.t) * g⁻¹ := by rw [hxt]
          _ = (g * x * g⁻¹) * (g * B.t * g⁻¹) := by group
          _ = (g * x * g⁻¹) * s := by rw [hgt]
    · -- injectivity
      rintro x y _ _ hxy
      exact mul_left_cancel (mul_right_cancel hxy)
    · -- surjectivity
      rintro y ⟨⟨hyH, hyo⟩, hyC⟩
      refine ⟨g⁻¹ * y * g, ⟨⟨?_, ?_⟩, ?_⟩, hconj_g y⟩
      · exact B.Hhat.mul_mem (B.Hhat.mul_mem (B.Hhat.inv_mem hgH) hyH) hgH
      · rw [show g⁻¹ * y * g = (MulAut.conj g⁻¹) y by rw [MulAut.conj_apply, inv_inv]]
        exact (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y).trans hyo
      · refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have hys : s * y = y * s := hyC s (Set.mem_singleton s)
        have hgts : g⁻¹ * s * g = B.t := by rw [← hgt]; group
        calc B.t * (g⁻¹ * y * g) = (g⁻¹ * s * g) * (g⁻¹ * y * g) := by rw [hgts]
          _ = g⁻¹ * (s * y) * g := by group
          _ = g⁻¹ * (y * s) * g := by rw [hys]
          _ = (g⁻¹ * y * g) * (g⁻¹ * s * g) := by group
          _ = (g⁻¹ * y * g) * B.t := by rw [hgts]
  -- ## For `t` the count is exactly the involutions of `H = C_G(t)`.
  have hHtEq : (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({B.t} : Set G))
      = Work.GW2.involutionSet B.H := by
    ext x
    constructor
    · rintro ⟨⟨hxH, hxo⟩, hxC⟩
      exact ⟨hxC, hxo⟩
    · rintro ⟨hxC, hxo⟩
      exact ⟨⟨B.H_le_Hhat hxC, hxo⟩, hxC⟩
  calc (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
      = (Work.GW2.involutionSet B.Hhat ∩ Subgroup.centralizer ({B.t} : Set G)).ncard :=
        hconj.symm
    _ = (Work.GW2.involutionSet B.H).ncard := by rw [hHtEq]
    _ = 3 + 2 * Nat.card D.K := hInvH

end Work.CORE3
