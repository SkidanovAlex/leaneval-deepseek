import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter

/-- Local sign change at a simple zero of a real function. -/
lemma simple_zero_sign_change {g : ℝ → ℝ} {s d : ℝ} (hs : g s = 0)
    (hd : d ≠ 0) (hder : HasDerivAt g d s) :
    ∃ δ > 0, (∀ x, x ∈ Set.Ioo (s - δ) s → g x * d < 0) ∧
             (∀ x, x ∈ Set.Ioo s (s + δ) → 0 < g x * d) := by
  have h_tend : Filter.Tendsto (slope g s) (nhdsWithin s ({s}ᶜ : Set ℝ)) (nhds d) :=
    hder.tendsto_slope
  have hd2 : 0 < d * d := mul_self_pos.mpr hd
  have hopen : IsOpen {y : ℝ | 0 < y * d} := by
    have h1 : {y : ℝ | 0 < y * d} = (fun y : ℝ => y * d) ⁻¹' (Set.Ioi 0) := rfl
    rw [h1]
    exact isOpen_Ioi.preimage (continuous_id.mul continuous_const)
  have h_ev : ∀ᶠ x in nhdsWithin s ({s}ᶜ : Set ℝ), 0 < slope g s x * d :=
    h_tend.eventually (hopen.mem_nhds (by simpa using hd2))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_ev
  obtain ⟨ε, hε, hεp⟩ := h_ev
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_Ioo] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hdist : dist x s < ε := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hne : x ∈ ({s}ᶜ : Set ℝ) := by simpa using (ne_of_lt hx2)
    have h := hεp hdist hne
    have hsl : slope g s x * d = (x - s)⁻¹ * (g x * d) := by
      rw [slope_fun_def]; simp only [vsub_eq_sub, smul_eq_mul, hs, sub_zero]; ring
    rw [hsl] at h
    have hxs : x - s < 0 := by linarith
    have heq : (x - s) * ((x - s)⁻¹ * (g x * d)) = g x * d := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt hxs), one_mul]
    rw [← heq]
    exact mul_neg_of_neg_of_pos hxs h
  · intro x hx
    rw [Set.mem_Ioo] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hdist : dist x s < ε := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hne : x ∈ ({s}ᶜ : Set ℝ) := by simpa using (ne_of_gt hx1)
    have h := hεp hdist hne
    have hsl : slope g s x * d = (x - s)⁻¹ * (g x * d) := by
      rw [slope_fun_def]; simp only [vsub_eq_sub, smul_eq_mul, hs, sub_zero]; ring
    rw [hsl] at h
    have hxs : 0 < x - s := by linarith
    have heq : (x - s) * ((x - s)⁻¹ * (g x * d)) = g x * d := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hxs), one_mul]
    rw [← heq]
    exact mul_pos hxs h

/-- On a zero-free interval a continuous function has constant sign. -/
lemma mul_pos_of_no_zero {g : ℝ → ℝ} {p q x y : ℝ}
    (hcont : ContinuousOn g (Set.Icc p q))
    (hz : ∀ t ∈ Set.Icc p q, g t ≠ 0)
    (hx : x ∈ Set.Icc p q) (hy : y ∈ Set.Icc p q) :
    0 < g x * g y := by
  have hpre : IsPreconnected (g '' Set.Icc p q) := isPreconnected_Icc.image g hcont
  have hord : (g '' Set.Icc p q).OrdConnected := hpre.ordConnected
  have hxg : g x ∈ g '' Set.Icc p q := ⟨x, hx, rfl⟩
  have hyg : g y ∈ g '' Set.Icc p q := ⟨y, hy, rfl⟩
  rcases lt_trichotomy (g x * g y) 0 with h | h | h
  · rcases mul_neg_iff.mp h with ⟨hgx, hgy⟩ | ⟨hgx, hgy⟩
    · have h0 : (0:ℝ) ∈ g '' Set.Icc p q := hord.out hyg hxg ⟨le_of_lt hgy, le_of_lt hgx⟩
      obtain ⟨c, hc, hc0⟩ := h0; exact (hz c hc hc0).elim
    · have h0 : (0:ℝ) ∈ g '' Set.Icc p q := hord.out hxg hyg ⟨le_of_lt hgx, le_of_lt hgy⟩
      obtain ⟨c, hc, hc0⟩ := h0; exact (hz c hc hc0).elim
  · exact absurd h (mul_ne_zero (hz x hx) (hz y hy))
  · exact h

/-- IVT: opposite signs at the endpoints force an interior zero. -/
lemma exists_zero_in_Ioo_of_mul_neg {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b)) (h : g a * g b < 0) :
    ∃ c ∈ Set.Ioo a b, g c = 0 := by
  have hpre : IsPreconnected (g '' Set.Icc a b) := isPreconnected_Icc.image g hcont
  have hord : (g '' Set.Icc a b).OrdConnected := hpre.ordConnected
  have ha : g a ∈ g '' Set.Icc a b := ⟨a, left_mem_Icc.mpr hab.le, rfl⟩
  have hb : g b ∈ g '' Set.Icc a b := ⟨b, right_mem_Icc.mpr hab.le, rfl⟩
  have h0 : (0:ℝ) ∈ g '' Set.Icc a b := by
    rcases mul_neg_iff.mp h with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩
    · exact hord.out hb ha ⟨le_of_lt hb0, le_of_lt ha0⟩
    · exact hord.out ha hb ⟨le_of_lt ha0, le_of_lt hb0⟩
  obtain ⟨c, hc, hc0⟩ := h0
  have hgane : g a ≠ 0 := fun hh => by rw [hh, zero_mul] at h; exact lt_irrefl 0 h
  have hgbne : g b ≠ 0 := fun hh => by rw [hh, mul_zero] at h; exact lt_irrefl 0 h
  obtain ⟨hca, hcb⟩ := hc
  refine ⟨c, ⟨?_, ?_⟩, hc0⟩
  · rcases lt_or_eq_of_le hca with h' | h'
    · exact h'
    · exfalso; rw [← h'] at hc0; exact hgane hc0
  · rcases lt_or_eq_of_le hcb with h' | h'
    · exact h'
    · exfalso; rw [h'] at hc0; exact hgbne hc0

/-- Elementary sign algebra. -/
lemma mul_pos_of_mul_neg_of_mul_neg {a b c : ℝ} (h1 : a * b < 0) (h2 : a * c < 0) : 0 < b * c := by
  have hane : a ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact lt_irrefl 0 h1
  have ha2 : 0 < a * a := mul_self_pos.mpr hane
  have hp : 0 < (a * b) * (a * c) := mul_pos_of_neg_of_neg h1 h2
  have hr : (a * b) * (a * c) = (a * a) * (b * c) := by ring
  rw [hr] at hp
  rcases mul_pos_iff.mp hp with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h (not_lt.mpr (le_of_lt ha2))

lemma mul_neg_of_mul_neg_of_mul_pos {a b c : ℝ} (h1 : a * b < 0) (h2 : 0 < a * c) : b * c < 0 := by
  have hane : a ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact lt_irrefl 0 h1
  have ha2 : 0 < a * a := mul_self_pos.mpr hane
  have hp : (a * b) * (a * c) < 0 := mul_neg_of_neg_of_pos h1 h2
  have hr : (a * b) * (a * c) = (a * a) * (b * c) := by ring
  rw [hr] at hp
  rcases mul_neg_iff.mp hp with ⟨_, hbc⟩ | ⟨hneg, _⟩
  · exact hbc
  · exact absurd hneg (not_lt.mpr (le_of_lt ha2))

/-- The inductive heart: for a continuous function on `[a,b]` whose interior zeros
are finite and simple, and with nonzero endpoint values, the number of interior
zeros is odd iff the endpoint values have opposite signs. -/
lemma main_claim (n : ℕ) : ∀ (a b : ℝ) (g : ℝ → ℝ), a < b →
    ContinuousOn g (Set.Icc a b) →
    ({s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0}).Finite →
    (∀ s : ℝ, s ∈ Set.Ioo a b → g s = 0 → ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt g d s) →
    g a ≠ 0 → g b ≠ 0 →
    Set.ncard {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0} = n →
    (Odd n ↔ g a * g b < 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b g hab hcont hfin hsimple hga hgb hn
    by_cases hn0 : n = 0
    · subst hn0
      have hS : {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0} = ∅ :=
        (Set.ncard_eq_zero (s := {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0}) hfin).mp hn
      constructor
      · intro hodd; exact absurd hodd (by rw [Nat.odd_iff]; decide)
      · intro hlt
        obtain ⟨c, hc, hc0⟩ := exists_zero_in_Ioo_of_mul_neg hab hcont hlt
        have hmem : c ∈ {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0} := ⟨hc, hc0⟩
        rw [hS] at hmem
        exact absurd hmem (by simp)
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      let Zab : Set ℝ := {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0}
      have hZabfin : Zab.Finite := hfin
      have hZabn : Zab.ncard = n := hn
      have hZabne : Zab.Nonempty := (Set.ncard_pos (s := Zab) hZabfin).mp (by omega)
      have htoF : hZabfin.toFinset.Nonempty := hZabfin.toFinset_nonempty.mpr hZabne
      set z : ℝ := hZabfin.toFinset.min' htoF with hzdef
      have hz_mem : z ∈ Zab := by
        rw [hzdef, ← hZabfin.mem_toFinset]; exact Finset.min'_mem _ _
      have hz_le : ∀ s ∈ Zab, z ≤ s := by
        intro s hs; rw [hzdef]; exact Finset.min'_le _ s (hZabfin.mem_toFinset.mpr hs)
      obtain ⟨hza, hzb⟩ : z ∈ Set.Ioo a b := hz_mem.1
      have hz0 : g z = 0 := hz_mem.2
      obtain ⟨d, hd, hder⟩ := hsimple z ⟨hza, hzb⟩ hz0
      obtain ⟨δ0, hδ0pos, hδ0L, hδ0R⟩ := simple_zero_sign_change hz0 hd hder
      set δ : ℝ := min δ0 (b - z) with hδdef
      have hδpos : 0 < δ := lt_min hδ0pos (by linarith)
      have hδle0 : δ ≤ δ0 := min_le_left _ _
      have hδleb : δ ≤ b - z := min_le_right _ _
      set w : ℝ := z + δ/2 with hwdef
      have hzw : z < w := by rw [hwdef]; linarith
      have hw_lt_b : w < b := by rw [hwdef]; linarith
      have hw_in : w ∈ Set.Ioo z (z + δ0) := by
        rw [Set.mem_Ioo, hwdef]; constructor <;> linarith
      have hgw_d : 0 < g w * d := hδ0R w hw_in
      have hgw_ne : g w ≠ 0 := by intro h; rw [h, zero_mul] at hgw_d; exact lt_irrefl 0 hgw_d
      let S' : Set ℝ := {s : ℝ | s ∈ Set.Ioo w b ∧ g s = 0}
      have hS'eq : S' = Zab \ {z} := by
        ext s; constructor
        · intro hs
          obtain ⟨hsw, hsb⟩ := hs.1
          refine ⟨⟨⟨by linarith, hsb⟩, hs.2⟩, ?_⟩
          simp only [Set.mem_singleton_iff]
          intro hsz; rw [hsz] at hsw; linarith
        · intro hs
          obtain ⟨hsZab, hsne⟩ := hs
          obtain ⟨hsa, hsb⟩ := hsZab.1
          have hs0 : g s = 0 := hsZab.2
          have hsne' : s ≠ z := by simpa [Set.mem_singleton_iff] using hsne
          have hsz : z < s := lt_of_le_of_ne (hz_le s hsZab) (Ne.symm hsne')
          have hws : w < s := by
            by_contra hcon
            have : s ∈ Set.Ioo z (z + δ0) := ⟨hsz, by linarith [not_lt.mp hcon]⟩
            have := hδ0R s this
            rw [hs0, zero_mul] at this; exact lt_irrefl 0 this
          exact ⟨⟨hws, hsb⟩, hs0⟩
      have hS'fin : S'.Finite := hZabfin.subset (fun s hs => by rw [hS'eq] at hs; exact hs.1)
      have hS'n : S'.ncard = n - 1 := by
        rw [hS'eq, Set.ncard_sdiff_singleton_of_mem hz_mem, hZabn]
      have hlt : S'.ncard < n := by omega
      have hcont' : ContinuousOn g (Set.Icc w b) :=
        hcont.mono (Set.Icc_subset_Icc (le_of_lt (lt_trans hza hzw)) le_rfl)
      have hsimple' : ∀ s : ℝ, s ∈ Set.Ioo w b → g s = 0 → ∃ e : ℝ, e ≠ 0 ∧ HasDerivAt g e s := by
        intro s hs hs0
        exact hsimple s ⟨by linarith [hza, hzw, hs.1], hs.2⟩ hs0
      have hih := ih S'.ncard hlt w b g hw_lt_b hcont' hS'fin hsimple' hgw_ne hgb rfl
      set y : ℝ := (max a (z - δ0) + z)/2 with hydef
      have hytop : max a (z - δ0) < z := max_lt hza (by linarith)
      have hya : a < y := by rw [hydef]; have := le_max_left a (z - δ0); linarith
      have hyz : y < z := by rw [hydef]; linarith
      have hylow : z - δ0 < y := by rw [hydef]; have := le_max_right a (z - δ0); linarith
      have hgy_d : g y * d < 0 := hδ0L y (by rw [Set.mem_Ioo]; exact ⟨hylow, hyz⟩)
      have hcont_ay : ContinuousOn g (Set.Icc a y) :=
        hcont.mono (Set.Icc_subset_Icc le_rfl (le_of_lt (lt_trans hyz hzb)))
      have hz_ay : ∀ t ∈ Set.Icc a y, g t ≠ 0 := by
        intro t ht ht0
        have hta : a < t := by
          rcases lt_or_eq_of_le ht.1 with h' | h'
          · exact h'
          · exfalso; rw [← h'] at ht0; exact hga ht0
        have htb : t < b := lt_of_le_of_lt ht.2 (lt_trans hyz hzb)
        have htZab : t ∈ Zab := ⟨⟨hta, htb⟩, ht0⟩
        exact absurd (hz_le t htZab) (not_le.mpr (lt_of_le_of_lt ht.2 hyz))
      have hga_gy : 0 < g a * g y :=
        mul_pos_of_no_zero hcont_ay hz_ay (left_mem_Icc.mpr (le_of_lt hya)) (right_mem_Icc.mpr (le_of_lt hya))
      have hga_d : g a * d < 0 := by
        have hgyne : g y ≠ 0 := by intro h; rw [h, mul_zero] at hga_gy; exact lt_irrefl 0 hga_gy
        have hgy2 : 0 < g y * g y := mul_self_pos.mpr hgyne
        have hp : (g a * g y) * (g y * d) < 0 := mul_neg_of_pos_of_neg hga_gy hgy_d
        have hr : (g a * g y) * (g y * d) = (g a * d) * (g y * g y) := by ring
        rw [hr] at hp
        rcases mul_neg_iff.mp hp with ⟨_, h⟩ | ⟨h, _⟩
        · exact absurd h (not_lt.mpr (le_of_lt hgy2))
        · exact h
      have hga_gw : g a * g w < 0 := by
        have h1 : d * g a < 0 := by rw [mul_comm]; exact hga_d
        have h2 : 0 < d * g w := by rw [mul_comm]; exact hgw_d
        exact mul_neg_of_mul_neg_of_mul_pos h1 h2
      have hgwgb_ne : g w * g b ≠ 0 := mul_ne_zero hgw_ne hgb
      have hnot : ¬ (g w * g b < 0) ↔ (0 < g w * g b) := by
        rw [not_lt]; exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hgwgb_ne), fun h => le_of_lt h⟩
      have hiff : (0 < g w * g b) ↔ (g a * g b < 0) := by
        constructor
        · intro h
          have h1 : g w * g a < 0 := by rw [mul_comm]; exact hga_gw
          exact mul_neg_of_mul_neg_of_mul_pos h1 h
        · intro h
          exact mul_pos_of_mul_neg_of_mul_neg hga_gw h
      have hn_eq : n = S'.ncard + 1 := by omega
      have hodd : Odd n ↔ ¬ Odd S'.ncard := by rw [hn_eq, Nat.odd_add_one]
      rw [hodd, hih, hnot]
      exact hiff

theorem odd_ncard_zeros_iff {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hfin : ({s : ℝ | g s = 0}).Finite)
    (hsub : {s : ℝ | g s = 0} ⊆ Set.Ioo a b)
    (hsimple : ∀ s : ℝ, g s = 0 → ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt g d s) :
    Odd (Set.ncard {s : ℝ | g s = 0}) ↔ g a * g b < 0 := by
  have hZeq : {s : ℝ | g s = 0} = {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0} := by
    ext s; constructor
    · intro hs; exact ⟨hsub hs, hs⟩
    · intro hs; exact hs.2
  have hfin' : ({s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0}).Finite :=
    hfin.subset (fun s hs => hs.2)
  have hga : g a ≠ 0 := by
    intro h
    have := hsub (show a ∈ {s : ℝ | g s = 0} from h)
    exact lt_irrefl a this.1
  have hgb : g b ≠ 0 := by
    intro h
    have := hsub (show b ∈ {s : ℝ | g s = 0} from h)
    exact lt_irrefl b this.2
  have hsimple' : ∀ s : ℝ, s ∈ Set.Ioo a b → g s = 0 → ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt g d s :=
    fun s _ hs => hsimple s hs
  have key := main_claim (Set.ncard {s : ℝ | s ∈ Set.Ioo a b ∧ g s = 0})
    a b g hab hcont hfin' hsimple' hga hgb rfl
  rw [hZeq]
  exact key

end Work.ELRig
