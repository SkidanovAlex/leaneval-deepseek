import Mathlib
import Submission.Core.FullPeriod

/-!
# D2-assembly: the superlevel cut integral is an interval integral

For a continuous UNIMODAL `q : [a,b] → [0,1]` (peak at `m`) and any level
`s`, the superlevel set `J_s := {t ∈ [a,b] | q(t) > s}` is an interval
(`Submission.Core.D2.superlevel_ordConnected`, step L2).  Hence, for any
continuous weight `w`, the "cut integral"

    ∫_a^b (if s < q t then w t else 0) dt

equals `∫_l^r w(t) dt` for suitable `a ≤ l ≤ r ≤ b` (take `l := sInf J_s`,
`r := sSup J_s`, with `l = r = a` when `J_s` is empty; the symmetric
difference of `J_s` and `[l,r]` has measure zero because both are intervals
with the same closure).  This reduces the per-level lower bound to
`Submission.Core.WInterval.w_interval_lower` (any-interval bound).

Prove the theorem below; you may add helper lemmas.  Do NOT change its
statement.  No sorries may remain in this file.
-/

noncomputable section

open scoped Real
open MeasureTheory
open Interval

namespace Submission.Core

/-- The superlevel set inside the open-at-`a` interval `(a,b]` is
order-connected for a unimodal `q`. -/
private lemma superlevel_Ioc_ordConnected (a b m s : ℝ) (q : ℝ → ℝ)
    (hu : UnimodalOn a b m q) :
    Set.OrdConnected {t : ℝ | a < t ∧ t ≤ b ∧ s < q t} := by
  let J : Set ℝ := {t : ℝ | a < t ∧ t ≤ b ∧ s < q t}
  let Jcc : Set ℝ := {t : ℝ | a ≤ t ∧ t ≤ b ∧ s < q t}
  change J.OrdConnected
  have hJcc : Jcc.OrdConnected := superlevel_ordConnected a b m s q hu
  have hJeq : J = Jcc ∩ Set.Ioc a b := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨le_of_lt hx.1, hx.2.1, hx.2.2⟩, hx.1, hx.2.1⟩
    · intro hx
      exact ⟨hx.2.1, hx.1.2.1, hx.1.2.2⟩
  rw [hJeq]
  exact Set.OrdConnected.inter hJcc (Set.ordConnected_Ioc (a := b) (b := a))

/-- For an order-connected nonempty bounded set of reals, the open interval
between its infimum and supremum is contained in the set. -/
private lemma Ioo_subset_of_ordConnected {s : Set ℝ} (hs : s.OrdConnected)
    (hne : s.Nonempty) :
    Set.Ioo (sInf s) (sSup s) ⊆ s := by
  intro z hz
  have hzl : sInf s < z := hz.1
  have hzr : z < sSup s := hz.2
  have hex1 : ∃ x ∈ s, x < z := by
    by_contra hnot
    have hforall : ∀ x ∈ s, z ≤ x := by
      intro x hx
      exact le_of_not_gt (by
        intro hxz
        exact hnot ⟨x, hx, hxz⟩)
    have hzle : z ≤ sInf s := le_csInf hne hforall
    linarith
  rcases hex1 with ⟨x, hx, hxz⟩
  have hex2 : ∃ y ∈ s, z < y := by
    by_contra hnot
    have hforall : ∀ y ∈ s, y ≤ z := by
      intro y hy
      exact le_of_not_gt (by
        intro hzy
        exact hnot ⟨y, hy, hzy⟩)
    have hlez : sSup s ≤ z := csSup_le hne hforall
    linarith
  rcases hex2 with ⟨y, hy, hzy⟩
  have hsub : Set.Icc x y ⊆ s := hs.out hx hy
  exact hsub ⟨le_of_lt hxz, le_of_lt hzy⟩

/-- **Superlevel cut = interval integral.**  For continuous unimodal `q` on
`[a,b]` (`a ≤ b`) and continuous `w`, the integral of `w` cut to the
superlevel set `{q > s}` equals the integral of `w` over some subinterval
`[l, r] ⊆ [a,b]`. -/
theorem superlevel_cut_interval (a b s : ℝ) (q w : ℝ → ℝ)
    (hle : a ≤ b)
    (hcont : ContinuousOn q (Set.Icc a b))
    (hu : ∃ m : ℝ, UnimodalOn a b m q)
    (hw : ContinuousOn w (Set.Icc a b)) :
    ∃ l r : ℝ, a ≤ l ∧ l ≤ r ∧ r ≤ b ∧
      (∫ t in a..b, if s < q t then w t else 0) = (∫ t in l..r, w t) := by
  rcases hu with ⟨m, hum⟩
  let J : Set ℝ := {t : ℝ | a < t ∧ t ≤ b ∧ s < q t}
  have hJoc : J.OrdConnected := by
    dsimp [J]
    exact superlevel_Ioc_ordConnected a b m s q hum
  by_cases hJempty : J = ∅
  · -- the superlevel set is empty inside (a,b]: the cut integral vanishes
    refine ⟨a, a, le_rfl, le_rfl, hle, ?_⟩
    have hfzero : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
        t ∈ Set.uIoc a b → (if s < q t then w t else 0) = 0 := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have ht' : t ∈ Set.Ioc a b := by
        rwa [Set.uIoc_of_le hle] at ht
      have hnot : ¬s < q t := by
        intro hlt
        have htJ : t ∈ J := by
          dsimp [J]
          exact ⟨ht'.1, ht'.2, hlt⟩
        simp [hJempty] at htJ
      simp [hnot]
    calc
      (∫ t in a..b, if s < q t then w t else 0)
          = (∫ t in a..b, (0 : ℝ)) := intervalIntegral.integral_congr_ae hfzero
      _ = 0 := intervalIntegral.integral_zero
      _ = (∫ t in a..a, w t) := intervalIntegral.integral_same.symm
  · -- nonempty superlevel set: take l = sInf J, r = sSup J
    have hJne : J.Nonempty := Set.nonempty_iff_ne_empty.mpr hJempty
    have hsubIcc : J ⊆ Set.Icc a b := by
      intro t ht
      exact ⟨le_of_lt ht.1, ht.2.1⟩
    have hbddB : BddBelow J := BddBelow.mono hsubIcc (bddBelow_Icc (a := b) (b := a))
    have hbddA : BddAbove J := BddAbove.mono hsubIcc (bddAbove_Icc (a := a) (b := b))
    let l : ℝ := sInf J
    let r : ℝ := sSup J
    have hl_a : a ≤ l := by
      dsimp [l]
      exact le_csInf hJne (fun t ht => le_of_lt ht.1)
    have hr_b : r ≤ b := by
      dsimp [r]
      exact csSup_le hJne (fun t ht => ht.2.1)
    have hl_r : l ≤ r := by
      dsimp [l, r]
      exact csInf_le_csSup hJne hbddB hbddA
    -- J = (l,r] up to the two endpoints (a null set), whence the
    -- corresponding indicator functions agree almost everywhere
    have hmem : ∀ t : ℝ, t ∉ ({l, r} : Set ℝ) → (t ∈ J ↔ t ∈ Set.Ioc l r) := by
      intro t htnot
      have htl : t ≠ l := by
        intro hEq
        apply htnot
        simp [hEq]
      have htr : t ≠ r := by
        intro hEq
        apply htnot
        simp [hEq]
      constructor
      · intro ht
        have htle_r : t ≤ r := by
          dsimp [r]
          exact le_csSup hbddA ht
        have hl_le_t : l ≤ t := by
          dsimp [l]
          exact csInf_le hbddB ht
        exact ⟨lt_of_le_of_ne hl_le_t (Ne.symm htl), htle_r⟩
      · intro ht
        have htr' : t < r := lt_of_le_of_ne ht.2 htr
        have hsub : Set.Ioo (sInf J) (sSup J) ⊆ J := Ioo_subset_of_ordConnected hJoc hJne
        exact hsub ⟨ht.1, htr'⟩
    have hae_pts : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), t ∉ ({l, r} : Set ℝ) := by
      exact ((Set.countable_insert (s := ({r} : Set ℝ)) (a := l)).2 (Set.countable_singleton r)).ae_notMem (volume : Measure ℝ)
    let g : ℝ → ℝ := fun t : ℝ => w t * (if t ∈ J then (1 : ℝ) else 0)
    let h : ℝ → ℝ := fun t : ℝ => w t * (if t ∈ Set.Ioc l r then (1 : ℝ) else 0)
    have hfun_ae : g =ᵐ[(volume : Measure ℝ)] h := by
      refine Filter.Eventually.mono hae_pts ?_
      intro t htnot
      have hiff := hmem t htnot
      dsimp [g, h]
      congr 1
      by_cases htJ : t ∈ J
      · have htR : t ∈ Set.Ioc l r := hiff.1 htJ
        simp [htJ, htR]
      · have htR : t ∉ Set.Ioc l r := by
          intro ht
          exact htJ (hiff.2 ht)
        simp [htJ, htR]
    have hL1 : (∫ t in a..b, if s < q t then w t else 0) = (∫ t in a..b, g t) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have ht' : t ∈ Set.Ioc a b := by
        rwa [Set.uIoc_of_le hle] at ht
      by_cases hlt : s < q t
      · have htJ : t ∈ J := by
          dsimp [J]
          exact ⟨ht'.1, ht'.2, hlt⟩
        simp [g, hlt, htJ]
      · have htJ : t ∉ J := by
          intro htJ
          exact hlt htJ.2.2
        simp [g, hlt, htJ]
    have hsupp_g : Function.support g ⊆ Set.Ioc a b := by
      intro t ht
      have htz : g t ≠ 0 := ht
      have htJ : t ∈ J := by
        by_contra hnot
        have hz : g t = 0 := by
          dsimp [g]
          simp [hnot]
        exact htz hz
      exact ⟨htJ.1, htJ.2.1⟩
    have hL2 : (∫ t in a..b, g t) = (∫ t : ℝ, g t) := by
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupp_g
    have hR1 : (∫ t in l..r, w t) = (∫ t in l..r, h t) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have ht' : t ∈ Set.Ioc l r := by
        rwa [Set.uIoc_of_le hl_r] at ht
      dsimp [h]
      simp [ht']
    have hsupp_h : Function.support h ⊆ Set.Ioc l r := by
      intro t ht
      have htz : h t ≠ 0 := ht
      have htR : t ∈ Set.Ioc l r := by
        by_contra hnot
        have hz : h t = 0 := by
          dsimp [h]
          simp [hnot]
        exact htz hz
      exact htR
    have hR2 : (∫ t in l..r, h t) = (∫ t : ℝ, h t) := by
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupp_h
    have hwhole : (∫ t : ℝ, g t) = (∫ t : ℝ, h t) := MeasureTheory.integral_congr_ae hfun_ae
    refine ⟨l, r, hl_a, hl_r, hr_b, ?_⟩
    calc
      (∫ t in a..b, if s < q t then w t else 0)
          = (∫ t in a..b, g t) := hL1
      _ = (∫ t : ℝ, g t) := hL2
      _ = (∫ t : ℝ, h t) := hwhole
      _ = (∫ t in l..r, h t) := hR2.symm
      _ = (∫ t in l..r, w t) := hR1.symm

end Submission.Core

end
