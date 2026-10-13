/-
  `slot_bound` : the telescoping inside one slot (step 6 of the ULPM proof).

  On an interval `(a,b)` free of the breakpoint family `B`, on which either no doubling ratio value
  is a bad scale (`Mid E`) or the ratio is constantly one bad scale, any two fibre values at points
  at depth `N` inside the slot are comparable up to the exponent of an element of `ExpSet E` and a
  factor `N`.

  The threshold `N₀` is chosen so that the total multiplicative deviation `∑_j β M_j^{-η}` along the
  dyadic chain (a geometric series, bounded by `tent_sum`) is smaller than `log₂ N₀`.  The band
  structure of the ratio (finite cluster set `E`) then pins the perturbation of `hdev` to a single
  `ρ ∈ E` (`band_const` + `eq_of_close_band`), or the ratio is constant on a bad scale, and the
  telescoping bound `slot_step` finishes.
-/
import Mathlib
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.slot_aux
import Submission.Work.WilC4.slot_step
import Submission.Work.WilC4.band_const
import Submission.Work.WilC4.eq_of_close_band
import Submission.Work.WilC4.isRpow_rpow
import Submission.Work.WilC4.mid_sep
import Submission.Work.WilC4.mid_band_unique
import Submission.Work.WilC4.mid_rpow_rat

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
open scoped Topology
namespace Work.WilC4

open Work.WilC4.Route (Gr InD valY ratioY eq_valY valY_mem)

theorem slot_bound {k : ℕ}
    {Y : Set (Fin (k + 2) → ℝ)} {B₀ B : Set (Fin (k + 1) → ℝ)} {E : Set ℝ}
    {η : ℚ} {β : ℝ} (hη : 0 < η) (hβ : 0 < β)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hsub : B₀ ⊆ B)
    (hst : Work.WilC4.ULPMStruct Y B₀)
    (hfmono : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
      MonotoneOn (Work.WilC4.Route.valY Y c) (Set.Ioo a b) ∨
        AntitoneOn (Work.WilC4.Route.valY Y c) (Set.Ioo a b))
    (hdev : ∃ R : ℝ, ∀ M : ℝ, R ≤ M → ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      Work.WilC4.IsDeepR B c M x → Work.WilC4.RatW Y c x w →
      ∃ ρ ∈ E, 0 < ρ ∧ |w / ρ - 1| ≤ β * M ^ (-(η : ℝ)))
    (hEfin : E.Finite) (hEne : ∃ ρ ∈ E, 0 < ρ)
    (hEsq : E ⊆ ({0} : Set ℝ) ∪ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ))) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (c : Fin k → ℝ) (a b x₁ x₂ y₁ y₂ : ℝ), 0 < a → a < b →
        (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
        ((∀ x ∈ Set.Ioo a b, ∀ w : ℝ, Work.WilC4.RatW Y c x w →
            w ∉ Work.WilC4.Mid E) ∨
          (∃ mid ∈ Work.WilC4.Mid E, ∀ x ∈ Set.Ioo a b, ∀ w : ℝ,
            Work.WilC4.RatW Y c x w → w = mid)) →
        0 < x₁ → 0 < x₂ → x₁ ≤ x₂ → (N : ℝ) * a < x₁ → (N : ℝ) * x₂ < b →
        Work.WilC4.Route.Gr Y c x₁ y₁ → Work.WilC4.Route.Gr Y c x₂ y₂ →
        ∃ q ∈ Work.WilC4.ExpSet E, ∃ t₁ t₂ : ℝ,
          Work.WilC4.IsRpow x₁ q t₁ ∧ Work.WilC4.IsRpow x₂ q t₂ ∧
          |y₂| * t₁ ≤ (N : ℝ) * (|y₁| * t₂) ∧
          |y₁| * t₂ ≤ (N : ℝ) * (|y₂| * t₁) := by
  classical
  have hη0 : (0:ℝ) < (η:ℝ) := by exact_mod_cast hη
  have hgood : GoodFibre Y B₀ := hst.1
  have hgoodB : GoodFibre Y B := fun c a b hab hfr =>
    hgood c a b hab (fun x hx hxB => hfr x hx (hsub hxB))
  obtain ⟨R, hR⟩ := hdev
  obtain ⟨δ, hδpos, hδsep⟩ := mid_sep hEfin
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ q ∈ ExpSet E, |(q:ℝ)| ≤ D := by
    obtain ⟨D, hDb⟩ := Set.Finite.bddAbove ((expSet_finite hEfin).image (fun q : ℚ => |(q:ℝ)|))
    exact ⟨D, fun q hq => hDb (Set.mem_image_of_mem (fun q : ℚ => |(q:ℝ)|) hq)⟩
  have hD0 : 0 ≤ D := by simpa using hD 0 (mem_expSet.mpr (Or.inl rfl))
  set c0 : ℝ := min δ (1/2) with hc0def
  have hc0pos : 0 < c0 := lt_min hδpos (by norm_num)
  set A : ℝ := 8 * (4:ℝ)^(η:ℝ) * β / (1 - (2:ℝ)^(-(η:ℝ))) + 4 * β * (8:ℝ)^(η:ℝ) with hAdef
  -- ## The threshold `N₀`
  have hev1 : ∀ᶠ N : ℕ in Filter.atTop, (2:ℝ) ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop 2
  have hev2 : ∀ᶠ N : ℕ in Filter.atTop, (8:ℝ) * R ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 * R)
  have hev3 : ∀ᶠ N : ℕ in Filter.atTop,
      β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) < c0 / 2 := by
    have h3 : Filter.Tendsto (fun N : ℕ => β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)))
        Filter.atTop (𝓝 (β * (8:ℝ)^(η:ℝ) * 0)) :=
      ((tendsto_rpow_neg_atTop hη0).comp tendsto_natCast_atTop_atTop).const_mul _
    have h0 : β * (8:ℝ)^(η:ℝ) * 0 = 0 := by ring
    rw [h0] at h3
    exact h3.eventually (eventually_lt_nhds (by linarith [hc0pos] : (0:ℝ) < c0/2))
  have hev4 : ∀ᶠ N : ℕ in Filter.atTop,
      A * (N:ℝ)^(-(η:ℝ)) + 2 * D ≤ Real.logb 2 (N:ℝ) := by
    have hlogb : Filter.Tendsto (fun N : ℕ => Real.logb 2 (N:ℝ)) Filter.atTop Filter.atTop :=
      (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hF : Filter.Tendsto (fun N : ℕ => A * (N:ℝ)^(-(η:ℝ)) + 2 * D)
        Filter.atTop (𝓝 (2 * D)) := by
      have h1 : Filter.Tendsto (fun N : ℕ => A * (N:ℝ)^(-(η:ℝ))) Filter.atTop (𝓝 (A * 0)) :=
        ((tendsto_rpow_neg_atTop hη0).comp tendsto_natCast_atTop_atTop).const_mul A
      simpa using h1.add_const (2 * D)
    have hdiff : Filter.Tendsto
        (fun N : ℕ => Real.logb 2 (N:ℝ) - (A * (N:ℝ)^(-(η:ℝ)) + 2 * D))
        Filter.atTop Filter.atTop := by
      have h := hlogb.atTop_add hF.neg
      simpa [sub_eq_add_neg] using h
    refine (hdiff.eventually_ge_atTop (2 * D)).mono (fun N hN => ?_)
    linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev1
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev2
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp hev3
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.mp hev4
  refine ⟨max 2 (max (max N₁ N₂) (max N₃ N₄)), le_max_left _ _, ?_⟩
  intro N hN c a b x₁ x₂ y₁ y₂ ha hab hfree hslot hx₁ hx₂ hx₁₂ hNax hNxb hGr₁ hGr₂
  have hcond1 : (2:ℝ) ≤ (N:ℝ) := hN₁ N (by omega)
  have hcond2 : (8:ℝ) * R ≤ (N:ℝ) := hN₂ N (by omega)
  have hcond3 : β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) < c0 / 2 := hN₃ N (by omega)
  have hcond4 : A * (N:ℝ)^(-(η:ℝ)) + 2 * D ≤ Real.logb 2 (N:ℝ) := hN₄ N (by omega)
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by linarith
  have hbigA : (8 * (4:ℝ)^(η:ℝ) * β / (1 - (2:ℝ)^(-(η:ℝ))) + 4 * β * (8:ℝ)^(η:ℝ))
      * (N:ℝ)^(-(η:ℝ)) + 2*D ≤ Real.logb 2 (N:ℝ) := by
    rw [hAdef] at hcond4; exact hcond4
  have hsmall : β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) ≤ 1/2 := by
    have h1 := le_of_lt hcond3
    have h2 : c0 ≤ 1/2 := min_le_right δ (1/2)
    linarith
  -- ## Basic membership on `(a,b)`
  have hax₁ : a < x₁ := by
    rcases lt_or_ge a 0 with h | h
    · linarith
    · exact lt_of_le_of_lt (le_mul_of_one_le_left h hN1r) hNax
  have hx₂b : x₂ < b := by nlinarith [hNxb, hx₂, hN1r]
  have hx₁b : x₁ < b := lt_of_le_of_lt hx₁₂ hx₂b
  have hbpos : 0 < b := lt_trans hx₂ hx₂b
  have hx₁I : x₁ ∈ Set.Ioo a b := ⟨hax₁, hx₁b⟩
  have hx₂I : x₂ ∈ Set.Ioo a b := ⟨lt_of_lt_of_le hax₁ hx₁₂, hx₂b⟩
  have hfree₀ : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀ := fun x hx hxB => hfree x hx (hsub hxB)
  have hx₁hb : x₁ < b/2 := by nlinarith [hNxb, hx₂, hx₁₂, hcond1]
  have h2x2b : 2 * x₂ < b := by nlinarith [hNxb, hcond1, hx₂]
  have hsign := valY_sign hgood hab hfree₀
  have habsmono : MonotoneOn (fun z => |valY Y c z|) (Set.Ioo a b) ∨
      AntitoneOn (fun z => |valY Y c z|) (Set.Ioo a b) := by
    rcases hsign with hp | hn
    · rcases hfmono c a b hab hfree with hm | ha'
      · exact Or.inl fun u hu v hv huv => by
          simpa only [abs_of_pos (hp u hu), abs_of_pos (hp v hv)] using hm hu hv huv
      · exact Or.inr fun u hu v hv huv => by
          simpa only [abs_of_pos (hp u hu), abs_of_pos (hp v hv)] using ha' hu hv huv
    · rcases hfmono c a b hab hfree with hm | ha'
      · exact Or.inr fun u hu v hv huv => by
          simpa only [abs_of_neg (hn u hu), abs_of_neg (hn v hv)] using neg_le_neg (hm hu hv huv)
      · exact Or.inl fun u hu v hv huv => by
          simpa only [abs_of_neg (hn u hu), abs_of_neg (hn v hv)] using neg_le_neg (ha' hu hv huv)
  rcases eq_or_lt_of_le hx₁₂ with heq | hlt
  · subst heq
    have hyeq : y₁ = y₂ := hfun c x₁ y₁ y₂ hGr₁ hGr₂
    refine ⟨0, mem_expSet.mpr (Or.inl rfl), 1, 1, ?_, ?_, ?_, ?_⟩
    · simpa using isRpow_rpow hx₁ 0
    · simpa using isRpow_rpow hx₁ 0
    · rw [hyeq]; nlinarith [abs_nonneg y₂, hN1r]
    · rw [hyeq]; nlinarith [abs_nonneg y₂, hN1r]
  · -- ## `x₁ < x₂`: the chain
    have hrat1 : 1 < x₂ / x₁ := (one_lt_div hx₁).mpr hlt
    have hlogpos : 0 < Real.logb 2 (x₂ / x₁) := Real.logb_pos (by norm_num) hrat1
    set K : ℕ := Nat.ceil (Real.logb 2 (x₂ / x₁)) with hKdef
    have hK1 : 1 ≤ K := by rw [hKdef]; exact Nat.one_le_ceil_iff.mpr hlogpos
    have hKlt : (K:ℝ) < Real.logb 2 (x₂ / x₁) + 1 := by
      rw [hKdef]; exact Nat.ceil_lt_add_one hlogpos.le
    have hpre : SlotPt x₁ (K-1) < x₂ := SlotPt_pre_lt hx₁ hx₂ hK1 (by rw [hKdef]; exact hKlt)
    have hK2 : SlotPt x₁ K < 2 * x₂ := SlotPt_K_lt hx₁ hx₂ (by rw [hKdef]; exact hKlt)
    have hx₂hb : x₂ < b/2 := by nlinarith [hNxb, hcond1, hx₂]
    have hmem : ∀ j : ℕ, j < K → SlotPt x₁ j ∈ Set.Ioo a (b/2) := by
      intro j hj
      exact ⟨lt_of_lt_of_le hax₁ (SlotPt_ge hx₁ j),
        lt_of_le_of_lt (SlotPt_mono hx₁ (Nat.le_pred_of_lt hj)) (lt_of_lt_of_le hpre hx₂hb.le)⟩
    have hmem_ab : ∀ j : ℕ, j < K → SlotPt x₁ j ∈ Set.Ioo a b := fun j hj =>
      ⟨(hmem j hj).1, lt_trans (hmem j hj).2 (by linarith)⟩
    have hmem2 : ∀ j : ℕ, j < K → 2 * SlotPt x₁ j ∈ Set.Ioo a b := by
      intro j hj
      have h1 : 2 * SlotPt x₁ j = SlotPt x₁ (j+1) := (SlotPt_succ x₁ j).symm
      refine ⟨lt_of_lt_of_le hax₁ (by rw [h1]; exact SlotPt_ge hx₁ (j+1)), ?_⟩
      rw [h1]
      exact lt_of_le_of_lt (SlotPt_mono hx₁ (Nat.succ_le_of_lt hj)) (lt_of_lt_of_le hK2 h2x2b.le)
    rcases hslot with hnoMid | ⟨mid, hmidMid, hmidconst⟩
    · -- ## Case (i): the ratio avoids `Mid E`, so it lives in a single band
      set a₁ : ℝ := max a 0 with ha₁def
      have ha₁b2 : a₁ < b/2 := max_lt (lt_trans hax₁ hx₁hb) (by linarith)
      have hfree₁ : ∀ x ∈ Set.Ioo a₁ (b/2), Fin.cons x c ∉ B₀ := by
        intro x hx hxB
        exact hfree₀ x ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_trans hx.2 (by linarith)⟩ hxB
      have hcontf : ContinuousOn (fun z => valY Y c z) (Set.Ioo a₁ (b/2)) :=
        valY_continuousOn_free hgood ha₁b2 hfree₁
      have hcontf_ab : ContinuousOn (fun z => valY Y c z) (Set.Ioo a b) :=
        valY_continuousOn_free hgood hab hfree₀
      have hcont2 : ContinuousOn (fun z => valY Y c (2*z)) (Set.Ioo a₁ (b/2)) := by
        refine hcontf_ab.comp (continuousOn_id.const_mul 2) ?_
        intro z hz
        refine ⟨?_, by linarith [hz.2, hbpos]⟩
        rcases lt_or_ge a 0 with h | h
        · have hz0 : 0 < z := by
            have : a₁ = 0 := max_eq_right h.le
            rw [this] at hz; exact hz.1
          linarith
        · linarith [hz.1, le_max_left a 0]
      have hnonzero : ∀ z ∈ Set.Ioo a₁ (b/2), valY Y c z ≠ 0 := by
        intro z hz
        exact (valY_gr_ne hgood hab hfree₀
          ⟨lt_of_le_of_lt (le_max_left _ _) hz.1, lt_trans hz.2 (by linarith)⟩).2
      have hcontratio : ContinuousOn (fun z => ratioY Y c z) (Set.Ioo a₁ (b/2)) :=
        hcont2.div hcontf hnonzero
      have hmem_both : ∀ z ∈ Set.Ioo a₁ (b/2), z ∈ Set.Ioo a b ∧ 2*z ∈ Set.Ioo a b := by
        intro z hz
        have hza : a < z := lt_of_le_of_lt (le_max_left a 0) hz.1
        have hzb : z < b := lt_trans hz.2 (by linarith)
        have h2za : a < 2*z := by
          rcases lt_or_ge a 0 with h | h
          · have : a₁ = 0 := max_eq_right h.le
            rw [this] at hz; linarith [hz.1]
          · linarith
        exact ⟨⟨hza, hzb⟩, ⟨h2za, by linarith [hz.2, hbpos]⟩⟩
      have hposratio : ∀ z ∈ Set.Ioo a₁ (b/2), 0 < ratioY Y c z := by
        intro z hz
        obtain ⟨hzI, h2zI⟩ := hmem_both z hz
        rcases hsign with hp | hn
        · exact div_pos (hp (2*z) h2zI) (hp z hzI)
        · exact div_pos_of_neg_of_neg (hn (2*z) h2zI) (hn z hzI)
      have havoidratio : ∀ z ∈ Set.Ioo a₁ (b/2), ratioY Y c z ∉ Mid E := by
        intro z hz hmid
        obtain ⟨hzI, h2zI⟩ := hmem_both z hz
        exact hnoMid z hzI (ratioY Y c z) (ratW_ratioY_of_free hfun hgoodB hab hfree hzI h2zI) hmid
      obtain ⟨ρ, hρE, hρpos, hρband⟩ :=
        band_const hEfin hEne ha₁b2 hcontratio hposratio havoidratio
      obtain ⟨q0, hq0⟩ : ∃ q0 : ℚ, ρ = (2:ℝ)^(q0:ℝ) := by
        rcases hEsq hρE with h0 | hrange
        · exact absurd h0 (ne_of_gt hρpos)
        · obtain ⟨q, hq⟩ := hrange; exact ⟨q, hq.symm⟩
      have hq0mem : q0 ∈ ExpSet E := mem_expSet.mpr (Or.inr (Or.inl ⟨ρ, hρE, hρpos, hq0⟩))
      refine ⟨q0, hq0mem, slot_step hη hβ hfun hgoodB hsign habsmono hab hfree ha hx₁ hx₂ hlt
        hcond1 hN1r hNax hNxb hGr₁ hGr₂ D hD0 hD hbigA hsmall q0 hq0mem ?_⟩
      intro j hj
      have hlj : SlotPt x₁ j < 2 * x₂ :=
        lt_of_le_of_lt (SlotPt_mono hx₁ (Nat.le_pred_of_lt hj)) (lt_of_lt_of_le hpre (by linarith))
      have hMj : R ≤ SlotM N x₁ b j := by
        have h1 := SlotM_ge hx₁ hNpos hbpos hNxb (SlotPt_ge hx₁ j) hlj
        linarith [h1, hcond2]
      have hdeepj : IsDeepR B c (SlotM N x₁ b j) (SlotPt x₁ j) :=
        isDeepR_SlotM hfree hx₁ hNpos hbpos hNax (hmem_ab j hj).1 (hmem_ab j hj).2
      have hratj : RatW Y c (SlotPt x₁ j) (ratioY Y c (SlotPt x₁ j)) :=
        ratW_ratioY_of_free hfun hgoodB hab hfree (hmem_ab j hj) (hmem2 j hj)
      obtain ⟨ρj, hρjE, hρjpos, hρjclose⟩ :=
        hR (SlotM N x₁ b j) hMj c (SlotPt x₁ j) (ratioY Y c (SlotPt x₁ j))
          (SlotPt_pos hx₁ j) hdeepj hratj
      have hεδ : β * (SlotM N x₁ b j) ^ (-(η:ℝ)) < δ := by
        have h1 : β * (SlotM N x₁ b j) ^ (-(η:ℝ))
            ≤ β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) := by
          have h2 : β * (SlotM N x₁ b j) ^ (-(η:ℝ)) ≤ β * ((N:ℝ)/8) ^ (-(η:ℝ)) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < (N:ℝ)/8)
                (SlotM_ge hx₁ hNpos hbpos hNxb (SlotPt_ge hx₁ j) hlj)
                (neg_nonpos.mpr hη0.le)) hβ.le
          have h3 : β * ((N:ℝ)/8) ^ (-(η:ℝ)) = β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) := by
            rw [div_rpow_neg hNpos (by norm_num : (0:ℝ) < 8)]; ring
          linarith [h2, h3]
        have h2 : c0 ≤ δ := min_le_left _ _
        linarith [h1, hcond3, h2]
      have heq := eq_of_close_band hEfin hδpos hδsep hρE hρpos hρjE hρjpos
        (hρband (SlotPt x₁ j) ⟨max_lt (hmem j hj).1 (SlotPt_pos hx₁ j), (hmem j hj).2⟩) hεδ hρjclose
      rw [heq, hq0] at hρjclose
      simpa using hρjclose
    · -- ## Case (ii): the ratio is constantly a bad scale
      obtain ⟨q0, hq0⟩ : ∃ q0 : ℚ, mid = (2:ℝ)^(q0:ℝ) := mid_rpow_rat hEsq hmidMid
      have hq0mem : q0 ∈ ExpSet E :=
        mem_expSet.mpr (Or.inr (Or.inr (by rw [← hq0]; exact hmidMid)))
      refine ⟨q0, hq0mem, slot_step hη hβ hfun hgoodB hsign habsmono hab hfree ha hx₁ hx₂ hlt
        hcond1 hN1r hNax hNxb hGr₁ hGr₂ D hD0 hD hbigA hsmall q0 hq0mem ?_⟩
      intro j hj
      have hmidj : ratioY Y c (SlotPt x₁ j) = mid :=
        hmidconst (SlotPt x₁ j) (hmem_ab j hj)
          (ratioY Y c (SlotPt x₁ j)) (ratW_ratioY_of_free hfun hgoodB hab hfree (hmem_ab j hj) (hmem2 j hj))
      have hz : ratioY Y c (SlotPt x₁ j) / (2:ℝ)^(q0:ℝ) - 1 = 0 := by
        rw [hmidj, hq0, div_self (by positivity : (2:ℝ)^(q0:ℝ) ≠ 0)]
        ring
      rw [hz, abs_zero]
      exact mul_nonneg hβ.le (Real.rpow_pos_of_pos (SlotM_pos hx₁ hNpos hbpos j) _).le

end Work.WilC4
