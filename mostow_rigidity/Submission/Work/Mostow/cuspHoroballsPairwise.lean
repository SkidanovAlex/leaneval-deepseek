import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.margulisCuspV2
import Submission.Work.Mostow.parabolicCommuteFix
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.parDisp_lipschitz_invariant
import Submission.Work.Mostow.cuspThinRegionBasic
import Submission.Work.Mostow.cuspThinRegionHoroball

/-!
# Pairwise disjoint cusp horoballs (the Margulis height)

For a lattice `Γ ≤ PO(n,1)` (`n ≥ 2`) and a `Γ`-invariant assignment `ξ ↦ ht ξ` on the set
`parFixed Γ` of parabolic fixed points, the horoballs `horoball ξ (ht ξ)` are pairwise disjoint.
This is the `Γ`-equivariant Margulis horoball packing of the cusps.

The construction is the Margulis one, in the form of the *thin regions*

`cuspThinRegion Γ ξ ε = {u | ∃ q : Γ, IsParabolic q ∧ bd q ξ = ξ ∧ hdist u (q • u) < ε}`

(`Submission/Work/Mostow/cuspThinRegionDefs.lean`):

* for `ε` below the Margulis threshold (`Work.Mostow.margulisCuspV2`), the thin regions of two
  *distinct* parabolic fixed points are disjoint (`cuspThinRegion_separation`, proved here from
  `margulisCuspV2` and the uniqueness of the boundary fixed point of a parabolic isometry,
  `Work.Mostow.pcf_parabolic_fixed_unique`);
* every thin region contains a horoball at its cusp (`crux_of_flatTrans`, proved here from the
  existence of a flat translation in the cusp stabiliser, `Work.Mostow.cuspParabolicFlatTrans`);
* the thin region does not fill `ℍⁿ`, uniformly in the level: the point of level `L` with flat
  coordinate `0` is not thin for `L` large, because the flat displacements of the parabolic
  elements of the stabiliser are bounded below by a positive constant
  (`cuspThinRegion_bounded`, proved from the discreteness of `Γ`).

The height is then `ht ξ = sSup {t | horoball ξ t ⊆ cuspThinRegion Γ ξ ε}`: it is
`Γ`-equivariant because the thin regions and the horoballs are transported by the action
(`cuspThinRegion_smul`), it is finite by the boundedness of the level set, and the horoballs are
disjoint because they lie in the pairwise disjoint thin regions.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-! ## 1. The translate of a thin region -/

lemma hptOf_zero_one (ξ : E n) : hptOf ξ 0 1 = 0 := by
  have h : (1 + (1 : ℝ) ^ 2 * ‖(0 : E n)‖ ^ 2) / (2 * 1) - 1 / 2 = 0 := by norm_num
  rw [hptOf, h]
  simp

/-! ## 3. The flat displacement of a parabolic at a flat point -/

lemma busemann_eq_log_lev (ξ u : E n) : busemann ξ u = Real.log (lev ξ u) := rfl

/-- **The displacement of the point of level `L` with flat coordinate `0`.** -/
lemma cosh_hdist_hptOf_zero (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    {ξ : E n} (hξ : ξ ∈ parFixed Γ) (q : Γ) (hqfix : bd (q : PO n 1) ξ = ξ) :
    ∀ L : ℝ, 0 < L → Real.cosh (hdist (hptOf ξ 0 L) ((q : PO n 1) • hptOf ξ 0 L))
      = 1 + (L ^ 2 / 2) * ‖yc ξ ((q : PO n 1) • (0 : E n))‖ ^ 2 := by
  intro L hL
  have hβ : busemann ξ ((q : PO n 1) • (0 : E n)) = 0 := by
    have h := hvan q ξ hξ hqfix
    rw [bCocy] at h
    rwa [hqfix] at h
  obtain ⟨A, v, -, -, -, hlevyc⟩ := stabFlatAction n hA hI ξ hξ.1 (q : PO n 1) hqfix hβ
  have hinner0 : inner ℝ (0 : E n) ξ = 0 := by simp
  have hlev0 : lev ξ (hptOf ξ 0 L) = L := (hptOf_level ξ hξ.1 L hL 0 hinner0).1
  have hyc0 : yc ξ (hptOf ξ 0 L) = 0 := (hptOf_level ξ hξ.1 L hL 0 hinner0).2
  have hlev1 : lev ξ ((q : PO n 1) • hptOf ξ 0 L) = L := (hlevyc 0 L hinner0 hL).1
  have hyc1 : yc ξ ((q : PO n 1) • hptOf ξ 0 L) = v := by
    have h := (hlevyc 0 L hinner0 hL).2
    simpa using h
  have hv : yc ξ ((q : PO n 1) • (0 : E n)) = v := by
    have h := (hlevyc 0 1 hinner0 one_pos).2
    rw [hptOf_zero_one] at h
    simpa using h
  have hform := levYcFormula (n := n) hξ.1 (hptOf ξ 0 L) ((q : PO n 1) • hptOf ξ 0 L)
  rw [hlev0, hlev1, hyc0, hyc1] at hform
  rw [hform, hv, div_self (ne_of_gt hL), Real.log_one, Real.cosh_zero, zero_sub, norm_neg]
  ring

/-! ## 4. A uniform positive lower bound for the flat displacements -/

lemma flat_vec_pos_lb (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    {ξ : E n} (hξ : ξ ∈ parFixed Γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q : Γ), IsParabolic (q : PO n 1) → bd (q : PO n 1) ξ = ξ →
      δ ≤ ‖yc ξ ((q : PO n 1) • (0 : E n))‖ := by
  by_contra hcon
  push_neg at hcon
  choose q hqpar hqfix hqlt using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  have hmemF : ∀ k : ℕ, hdist (0 : E n) ((q k : PO n 1) • (0 : E n)) ≤ 2 := by
    intro k
    have hcosh := cosh_hdist_hptOf_zero n hA hI Γ hvan hξ (q k) (hqfix k) 1 one_pos
    rw [hptOf_zero_one] at hcosh
    have hlt : ‖yc ξ ((q k : PO n 1) • (0 : E n))‖ < 1 := by
      have h1 : ‖yc ξ ((q k : PO n 1) • (0 : E n))‖ < 1 / ((k : ℝ) + 1) := hqlt k
      have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      linarith
    have hcosh2 : (3 : ℝ) / 2 ≤ Real.cosh 2 := by
      rw [Real.cosh_eq]
      have h1 : (4 : ℝ) < Real.exp 2 := by
        have h2 : Real.exp 2 = Real.exp (1 + 1 : ℝ) := by norm_num
        rw [h2, Real.exp_add]
        have h3 := Real.exp_one_gt_two
        nlinarith [Real.exp_pos (1 : ℝ)]
      have h4 := Real.exp_pos (-2 : ℝ)
      linarith
    have hb : Real.cosh (hdist (0 : E n) ((q k : PO n 1) • (0 : E n))) ≤ Real.cosh 2 := by
      rw [hcosh]
      nlinarith [norm_nonneg (yc ξ ((q k : PO n 1) • (0 : E n)))]
    have := (Real.cosh_le_cosh.mp hb)
    rw [abs_of_nonneg (hdist_nonneg (0 : E n) _), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at this
    exact this
  have hfinite : ({γ : Γ | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ 2}).Finite :=
    finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc 2
  have hrange : (Set.range q).Finite :=
    hfinite.subset (fun γ hγ => by obtain ⟨k, rfl⟩ := hγ; exact hmemF k)
  obtain ⟨q₀, hq₀mem, hq₀inf⟩ : ∃ q₀ ∈ Set.range q, ({k : ℕ | q k = q₀}).Infinite := by
    by_contra h'
    have h'ann : ∀ b ∈ Set.range q, ({k : ℕ | q k = b}).Finite := by
      intro b hb
      by_contra hfin
      exact h' ⟨b, hb, hfin⟩
    have hunion : (⋃ b ∈ Set.range q, {k : ℕ | q k = b}) = Set.univ := by
      ext k
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨q k, Set.mem_range_self k, rfl⟩
    have hfin : (Set.univ : Set ℕ).Finite := by
      rw [← hunion]
      exact hrange.biUnion h'ann
    exact Set.infinite_univ hfin
  obtain ⟨k₀, hk₀⟩ := hq₀mem
  have hq₀fix : bd (q₀ : PO n 1) ξ = ξ := by rw [← hk₀]; exact hqfix k₀
  have hpar₀ : IsParabolic (q₀ : PO n 1) := by rw [← hk₀]; exact hqpar k₀
  have hzero : yc ξ ((q₀ : PO n 1) • (0 : E n)) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    by_contra hnot
    push_neg at hnot
    obtain ⟨k, hkq, hkk⟩ := hq₀inf.exists_gt ⌈1 / ‖yc ξ ((q₀ : PO n 1) • (0 : E n))‖⌉₊
    have hkq' : q k = q₀ := hkq
    have hlt1 : 1 / ((k : ℝ) + 1) < ‖yc ξ ((q₀ : PO n 1) • (0 : E n))‖ := by
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hkR' : (⌈1 / ‖yc ξ ((q₀ : PO n 1) • (0 : E n))‖⌉₊ : ℝ) < (k : ℝ) := by
        exact_mod_cast hkk
      have h1 : 1 / ‖yc ξ ((q₀ : PO n 1) • (0 : E n))‖ < (k : ℝ) + 1 := by
        have hceil := Nat.le_ceil (1 / ‖yc ξ ((q₀ : PO n 1) • (0 : E n))‖)
        push_cast
        linarith
      have h2 : 1 < ((k : ℝ) + 1) * ‖yc ξ ((q₀ : PO n 1) • (0 : E n))‖ := by
        rw [div_lt_iff₀ hnot] at h1
        linarith
      rw [div_lt_iff₀ hkpos]
      linarith
    have hqk : ‖yc ξ ((q k : PO n 1) • (0 : E n))‖ < 1 / ((k : ℝ) + 1) := hqlt k
    rw [hkq'] at hqk
    linarith
  have hlev₀ : lev ξ ((q₀ : PO n 1) • (0 : E n)) = 1 := by
    have hβ : busemann ξ ((q₀ : PO n 1) • (0 : E n)) = 0 := by
      have h := hvan q₀ ξ hξ hq₀fix
      rw [bCocy] at h
      rwa [hq₀fix] at h
    obtain ⟨A, v, -, -, -, hlevyc⟩ := stabFlatAction n hA hI ξ hξ.1 (q₀ : PO n 1) hq₀fix hβ
    have h := (hlevyc 0 1 (by simp) one_pos).1
    rw [hptOf_zero_one] at h
    exact h
  have hfixpt : (q₀ : PO n 1) • (0 : E n) = 0 := by
    have h := hptOf_yc ξ hξ.1 (lev ξ ((q₀ : PO n 1) • (0 : E n))) (by rw [hlev₀]; norm_num)
      ((q₀ : PO n 1) • (0 : E n)) rfl
    rw [hlev₀, hzero] at h
    rw [← h, hptOf_zero_one]
  exact hpar₀.1 (0 : E n) hfixpt

/-! ## 5. The thin region does not fill the space -/

lemma cuspThinRegion_bounded (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    {ξ : E n} (hξ : ξ ∈ parFixed Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ hptOf ξ 0 L ∉ cuspThinRegion Γ ξ ε := by
  obtain ⟨δ, hδpos, hδ⟩ := flat_vec_pos_lb n hn hA hI Γ hdisc hvan hξ
  set c : ℝ := Real.sqrt (2 * (Real.cosh ε - 1)) with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact Real.sqrt_pos.mpr (by linarith [Real.one_lt_cosh.mpr (ne_of_gt hε)])
  refine ⟨(c + 1) / δ, by positivity, ?_⟩
  intro hmem
  obtain ⟨q, hqpar, hqfix, hqd⟩ := hmem
  have hcosh := cosh_hdist_hptOf_zero n hA hI Γ hvan hξ q hqfix ((c + 1) / δ) (by positivity)
  have hb : Real.cosh (hdist (hptOf ξ 0 ((c + 1) / δ)) ((q : PO n 1) • hptOf ξ 0 ((c + 1) / δ)))
      ≥ Real.cosh ε := by
    rw [hcosh]
    have h1 : δ ≤ ‖yc ξ ((q : PO n 1) • (0 : E n))‖ := hδ q hqpar hqfix
    have hDpos : 0 < (c + 1) / δ := by positivity
    have hkey : c ≤ ((c + 1) / δ) * ‖yc ξ ((q : PO n 1) • (0 : E n))‖ := by
      have h2 : ((c + 1) / δ) * δ = c + 1 := by
        rw [div_mul_cancel₀ _ (ne_of_gt hδpos)]
      calc c ≤ c + 1 := by linarith
        _ = ((c + 1) / δ) * δ := h2.symm
        _ ≤ ((c + 1) / δ) * ‖yc ξ ((q : PO n 1) • (0 : E n))‖ :=
            mul_le_mul_of_nonneg_left h1 hDpos.le
    have hcoshε : Real.cosh ε = 1 + c ^ 2 / 2 := by
      rw [hc, Real.sq_sqrt (by linarith [Real.one_le_cosh ε])]
      ring
    rw [hcoshε]
    have h3 : c ^ 2 ≤ (((c + 1) / δ) * ‖yc ξ ((q : PO n 1) • (0 : E n))‖) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hcpos) hkey 2
    nlinarith [h3]
  have hge : hdist (hptOf ξ 0 ((c + 1) / δ)) ((q : PO n 1) • hptOf ξ 0 ((c + 1) / δ)) ≥ ε := by
    have h1 : 0 ≤ hdist (hptOf ξ 0 ((c + 1) / δ)) ((q : PO n 1) • hptOf ξ 0 ((c + 1) / δ)) :=
      hdist_nonneg _ _
    have := (Real.cosh_le_cosh.mp hb)
    rw [abs_of_nonneg h1, abs_of_nonneg (le_of_lt hε)] at this
    exact this
  linarith [hqd]

/-! ## 6. Assembly -/

lemma csSup_shift (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) (c : ℝ) :
    sSup {t : ℝ | t - c ∈ S} = c + sSup S := by
  have hbdd' : BddAbove {t : ℝ | t - c ∈ S} :=
    ⟨c + sSup S, fun t ht => by linarith [le_csSup hbdd ht]⟩
  have hne' : ({t : ℝ | t - c ∈ S}).Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨c + s, by simpa using hs⟩
  apply le_antisymm
  · apply csSup_le hne'
    intro t ht
    linarith [le_csSup hbdd ht]
  · have h1 : sSup S ≤ sSup {t : ℝ | t - c ∈ S} - c := by
      apply csSup_le hne
      intro s hs
      have h3 : c + s ∈ {t : ℝ | t - c ∈ S} := by
        simp only [Set.mem_ofPred_eq]
        rw [add_sub_cancel_left]
        exact hs
      linarith [le_csSup hbdd' h3]
    linarith

/-- Membership form of the `Γ`-action on horoballs. -/
lemma smul_mem_horoball_iff (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (γ : Γ) {ξ : E n} (hξ : ξ ∈ Sph n) (t : ℝ) (w : E n) :
    (γ : PO n 1) • w ∈ horoball (bd (γ : PO n 1) ξ) t
      ↔ w ∈ horoball ξ (t - bCocy (γ : PO n 1) ξ) := by
  have hIk : HypIsoData n := HypIsoData.ofProp hI
  simp only [horoball, Set.mem_ofPred_eq]
  have hbus : busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • w)
      = busemann ξ w + bCocy (γ : PO n 1) ξ := hIk.busemann_cocycle (γ : PO n 1) ξ w hξ
  rw [hbus]
  constructor <;> intro h <;> linarith

lemma horoball_sSup_sub {Γ : Subgroup (PO n 1)} {ξ : E n} {ε : ℝ} {S : Set ℝ}
    (hne : S.Nonempty) (hS : ∀ t ∈ S, horoball ξ t ⊆ cuspThinRegion Γ ξ ε) :
    horoball ξ (sSup S) ⊆ cuspThinRegion Γ ξ ε := by
  intro u hu
  simp only [horoball, Set.mem_ofPred_eq] at hu
  have hex : ∃ t ∈ S, busemann ξ u < t := by
    by_contra h
    push_neg at h
    have hle : sSup S ≤ busemann ξ u := csSup_le hne h
    linarith
  obtain ⟨t, htS, htu⟩ := hex
  exact hS t htS (by simpa only [horoball, Set.mem_ofPred_eq] using htu)

theorem main_of_crux (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (hcrux : ∀ (ξ : E n), ξ ∈ parFixed Γ → ∀ ε : ℝ, 0 < ε →
      ∃ t : ℝ, horoball ξ t ⊆ cuspThinRegion Γ ξ ε) :
    ∃ ht : Submission.Mostow.E n → ℝ, Work.Mostow.IsEquivHeight Γ (Work.Mostow.parFixed Γ) ht ∧
      (Work.Mostow.parFixed Γ).Pairwise
        (fun ξ η => Disjoint (Submission.Mostow.horoball ξ (ht ξ))
          (Submission.Mostow.horoball η (ht η))) := by
  obtain ⟨ε, hεpos, hεsep⟩ := cuspThinRegion_separation n hn hA hI Γ hΓ.1
  have hne : ∀ ξ ∈ parFixed Γ, ({t : ℝ | horoball ξ t ⊆ cuspThinRegion Γ ξ ε}).Nonempty :=
    fun ξ hξ => hcrux ξ hξ ε hεpos
  have hbdd : ∀ ξ ∈ parFixed Γ, BddAbove {t : ℝ | horoball ξ t ⊆ cuspThinRegion Γ ξ ε} := by
    intro ξ hξ
    obtain ⟨L, hLpos, hLmem⟩ := cuspThinRegion_bounded n hn hA hI Γ hΓ.1 hvan hξ hεpos
    refine ⟨Real.log L, fun t ht => ?_⟩
    refine not_lt.mp (fun hlt => ?_)
    have hlevL : lev ξ (hptOf ξ 0 L) = L := (hptOf_level ξ hξ.1 L hLpos 0 (by simp)).1
    have hmem : hptOf ξ 0 L ∈ horoball ξ t := by
      simp only [horoball, Set.mem_ofPred_eq]
      rw [busemann_eq_log_lev, hlevL]
      exact hlt
    exact hLmem (ht hmem)
  refine ⟨fun ξ => sSup {t : ℝ | horoball ξ t ⊆ cuspThinRegion Γ ξ ε}, ?_, ?_⟩
  · intro γ ξ hξ
    change sSup {t : ℝ | horoball (bd (γ : PO n 1) ξ) t ⊆ cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε}
      = sSup {t : ℝ | horoball ξ t ⊆ cuspThinRegion Γ ξ ε} + bCocy (γ : PO n 1) ξ
    set c : ℝ := bCocy (γ : PO n 1) ξ with hc
    have hsinv : ∀ t : ℝ, (horoball (bd (γ : PO n 1) ξ) t ⊆ cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε)
        ↔ (horoball ξ (t - c) ⊆ cuspThinRegion Γ ξ ε) := by
      intro t
      have hiff : ∀ w : E n, ((γ : PO n 1) • w ∈ horoball (bd (γ : PO n 1) ξ) t)
          ↔ (w ∈ horoball ξ (t - c)) := by
        intro w
        have h := smul_mem_horoball_iff hA hI Γ γ hξ.1 t w
        rw [← hc] at h
        exact h
      constructor
      · intro h v hv
        have h1 : (γ : PO n 1) • v ∈ cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε := h ((hiff v).mpr hv)
        exact (smul_mem_cuspThinRegion hA hI Γ γ hξ.1 ε v).mp h1
      · intro h w hw
        have h1 : (γ : PO n 1)⁻¹ • w ∈ cuspThinRegion Γ ξ ε := by
          apply h
          have h2 : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) ∈ horoball (bd (γ : PO n 1) ξ) t := by
            have h3 : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) = w := by
              rw [← POBasic.ofProp hA |>.mul_smul, mul_inv_cancel, POBasic.ofProp hA |>.one_smul]
            rwa [h3]
          exact (hiff ((γ : PO n 1)⁻¹ • w)).mp h2
        have h3 : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) ∈ cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε :=
          (smul_mem_cuspThinRegion hA hI Γ γ hξ.1 ε ((γ : PO n 1)⁻¹ • w)).mpr h1
        rwa [show (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) = w from by
          rw [← POBasic.ofProp hA |>.mul_smul, mul_inv_cancel, POBasic.ofProp hA |>.one_smul]] at h3
    have hseteq : {t : ℝ | horoball (bd (γ : PO n 1) ξ) t ⊆ cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε}
        = {t : ℝ | t - c ∈ {s : ℝ | horoball ξ s ⊆ cuspThinRegion Γ ξ ε}} := by
      ext t
      simp only [Set.mem_ofPred_eq]
      exact hsinv t
    rw [hseteq, csSup_shift _ (hne ξ hξ) (hbdd ξ hξ) c, hc]
    ring
  · intro ξ hξ η hη hne'
    rw [Set.disjoint_left]
    intro u hu hu'
    have h1 : u ∈ cuspThinRegion Γ ξ ε := horoball_sSup_sub (hne ξ hξ) (fun t ht => ht) hu
    have h2 : u ∈ cuspThinRegion Γ η ε := horoball_sSup_sub (hne η hη) (fun t ht => ht) hu'
    exact Set.disjoint_left.mp (hεsep ξ hξ η hη hne') h1 h2


/-- **Pairwise disjoint cusp horoballs.**  A lattice `Γ ≤ PO(n,1)`, `n ≥ 2`, admits a
`Γ`-equivariant height `ht` on its set of parabolic fixed points whose horoballs are pairwise
disjoint (the Margulis/Shimizu horoball packing of the cusps). -/
theorem cuspHoroballsPairwise (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0) :
    ∃ ht : Submission.Mostow.E n → ℝ, Work.Mostow.IsEquivHeight Γ (Work.Mostow.parFixed Γ) ht ∧
      (Work.Mostow.parFixed Γ).Pairwise
        (fun ξ η => Disjoint (Submission.Mostow.horoball ξ (ht ξ))
          (Submission.Mostow.horoball η (ht η))) :=
  main_of_crux n hn hA hI hBb Γ hΓ hvan
    (fun ξ hξ => cuspThinRegion_horoball n hn hA hI Γ hΓ hvan hξ)

end

end Work.Mostow
