import Mathlib
import Submission.Work.Drive.oFatDefsS
import Submission.Work.Drive.ofatObstructionS_edges
import Submission.Work.Drive.ofatObstructionS_closed
import Submission.Work.Drive.components_bounded_of_no_spreadQuadS
import Submission.Work.Drive.fatMiddle_slab_hmax
import Submission.Work.Drive.noMiddle_near_farthest
import Submission.Work.Drive.noMiddle_wrap
import Submission.Work.Drive.separation_of_far_parameters
import Submission.Work.Drive.stripCrosscutAvoidingO_of_isClosed_finite_fibre
import Submission.Work.Drive.crosscut_or_spreadQuad
import Submission.Work.Drive.ofatEndgameSWiring

/-!
# `E3′`: the dichotomy of the lead's uniform-`ρ₀` design (`NOTES_LEAD_endgameUniform.md` §1,
with the wrap disjunct handled by `NOTES_LEAD_E3prime_wrap.md`)

`Work.Drive.crosscut_or_spreadQuadS` is `Work.Drive.crosscut_or_spreadQuad` with the obstruction set
enlarged to `Work.Drive.OFatObstructionS r ρ δs` (and the extra wrap-freeness hypothesis `hwrap`),
and `Work.Drive.crosscut_or_spreadQuad_of_closeS` is the `C²`-ball form consumed by
`Work.Drive.OFatE3S`; the last two lemmas discharge `Work.Drive.OFatE3S` from it.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

open scoped unitInterval

/-- **`E3′` of the lead's uniform-`ρ₀` design.**  Either `r` has a `δ`-spread quadrisecant
(`δ = min ρ (min (2η) (2s/V))`), or the period strip carries a bottom–top crosscut avoiding
`Work.Drive.OFatObstructionS r ρ δs`.  The hypothesis `hwrap` (supplied on the `C²`-ball by
`Work.Drive.noMiddle_wrap`) empties the wrap disjunct of `ShortMid`. -/
theorem crosscut_or_spreadQuadS {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r)
    {ρ t₀ η δs ηc s V : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hηP : 2 * η < period)
    (hmax : ∀ t : ℝ, ‖r t‖ ≤ ‖r t₀‖)
    (hslab : ∀ u : ℝ, FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)|)
    (hηc : 0 < ηc) (hηηc : 2 * η ≤ ηc)
    (hnear : ∀ c : ℝ, (∀ t : ℝ, ‖r t‖ ≤ ‖r c‖) → ∀ a y u : ℝ, 0 < y → y < period →
      c - ηc ≤ a → a ≤ c + ηc → c - ηc ≤ a + y → a + y ≤ c + ηc →
      a ≤ u → u ≤ a + y → r u ∉ openSegment ℝ (r a) (r (a + y)))
    (hδs : 0 < δs) (hδsηc : δs ≤ ηc / 2) (hδsP : δs < period / 2)
    (hwrap : ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δs → a ≤ u → u ≤ a + y →
      r u ∉ openSegment ℝ (r a) (r (a + y)))
    (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    (hlip : ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ V * dist a b) :
    (∃ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)) ∨
    StripCrosscutAvoidingOFatS r ρ δs := by
  by_cases hspread : ∃ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)
  · exact Or.inl hspread
  · refine Or.inr ?_
    have hbdd : ∀ z : ℝ × ℝ, z ∈ OFatObstructionS r ρ δs →
        Bornology.IsBounded (Prod.fst '' connectedComponentIn (OFatObstructionS r ρ δs) z) :=
      components_bounded_of_no_spreadQuadS hr hρ hη hηP hmax hslab hηc hηηc hnear hδs hδsηc
        hwrap hs hV hsep hlip htc hinfl
        (fun a b z w hδ hmid => hspread ⟨a, b, z, w, hδ, hmid.1, hmid.2⟩)
    obtain ⟨δ, hδpos, hbound⟩ := ofatObstructionS_edges hr hinfl hρ hδs hδsP
    have hstrip : OFatObstructionS r ρ δs ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < period} := by
      rintro q (hq | hq)
      · rcases hq with hq | hq
        · exact ⟨(mem_OFatR_iff.mp hq).1, (mem_OFatR_iff.mp hq).2.1⟩
        · exact ⟨(mem_TCset_iff.mp hq).1, (mem_TCset_iff.mp hq).2.1⟩
      · exact ⟨hq.1, hq.2.1⟩
    have haway : Disjoint (closure (OFatObstructionS r ρ δs))
        {z : ℝ × ℝ | z.2 ≤ 0 ∨ period ≤ z.2} := by
      rw [Set.disjoint_left]
      intro q hq hq'
      obtain ⟨hb1, hb2⟩ := hbound q hq
      rcases hq' with h | h <;> linarith
    obtain ⟨γ, h0, h1, hint⟩ :=
      exists_crosscut_period (isClosed_OFatObstructionS hr hinfl hρ) hstrip haway hbdd
    exact ⟨γ, h0, h1, (fun t ht0 ht1 => ⟨(hint t ht0 ht1).1, (hint t ht0 ht1).2.1⟩),
      (fun t ht0 ht1 => (hint t ht0 ht1).2.2)⟩

/-- **`E3′` uniformly over the `C²`-ball of a reference knot** (the lead's §1 statement, with the
wrap constants `εw, δw` of `Work.Drive.noMiddle_wrap` folded into `ε₁` and `δsmax`). -/
theorem crosscut_or_spreadQuad_of_closeS {r₀ : ℝ → Space} (hr₀ : IsSmoothKnot r₀) {V : ℝ}
    (hVpos : 0 < V) (hvel₀ : ∀ t : ℝ, ‖velocity r₀ t‖ ≤ V) :
    ∃ ε₁ δsmax : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < δsmax ∧
      ∀ {ρ δs : ℝ}, 0 < ρ → 0 < δs → δs ≤ δsmax →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ r' : ℝ → Space, IsSmoothKnot r' → TangentChordGP r' →
            (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
            (∀ t : ℝ, ‖r' t - r₀ t‖ < ε₁ ∧ ‖velocity r' t - velocity r₀ t‖ < ε₁ ∧
              ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < ε₁) →
            ((∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
                IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
                IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)) ∨
              StripCrosscutAvoidingOFatS r' ρ δs) := by
  obtain ⟨εs, hεspos, hs⟩ := separation_of_far_parameters hr₀
  obtain ⟨εa, hεapos, hE3a⟩ := fatMiddle_slab_hmax hr₀
  obtain ⟨ε₃, hε₃pos, ηc, hηcpos, hnear₀⟩ := noMiddle_near_farthest hr₀
  obtain ⟨εw, δw, hεwpos, hδwpos, hwrap₀⟩ := noMiddle_wrap hr₀
  refine ⟨min (min εs εa) (min (min ε₃ εw) 1),
    min (min (ηc / 2) (period / 4)) δw,
    lt_min (lt_min hεspos hεapos) (lt_min (lt_min hε₃pos hεwpos) one_pos),
    le_trans (min_le_right _ _) (min_le_right _ _),
    lt_min (lt_min (div_pos hηcpos (by norm_num)) (div_pos period_pos (by norm_num))) hδwpos,
    ?_⟩
  have hε1s : min (min εs εa) (min (min ε₃ εw) 1) ≤ εs :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hε1a : min (min εs εa) (min (min ε₃ εw) 1) ≤ εa :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hε13 : min (min εs εa) (min (min ε₃ εw) 1) ≤ ε₃ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε1w : min (min εs εa) (min (min ε₃ εw) 1) ≤ εw :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε11 : min (min εs εa) (min (min ε₃ εw) 1) ≤ 1 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  intro ρ δs hρ hδs hδsδsmax
  obtain ⟨s, hspos, hsep₀⟩ := hs ρ hρ
  obtain ⟨η₀, hη₀pos, hslab₀⟩ := hE3a ρ hρ
  set η : ℝ := min η₀ (min (ηc / 2) (period / 4)) with hηdef
  have hηpos : 0 < η := lt_min hη₀pos (lt_min (by positivity) (by linarith [period_pos]))
  have hηηc : 2 * η ≤ ηc := by
    have h1 : η ≤ ηc / 2 := by
      rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hηP : 2 * η < period := by
    have h1 : η ≤ period / 4 := by
      rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [period_pos]
  have hδsηc : δs ≤ ηc / 2 := le_trans hδsδsmax (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδsδw : δs ≤ δw := le_trans hδsδsmax (min_le_right _ _)
  have hδsP : δs < period / 2 := by
    have h1 : δs ≤ period / 4 :=
      le_trans hδsδsmax (le_trans (min_le_left _ _) (min_le_right _ _))
    linarith [period_pos]
  refine ⟨min ρ (min (2 * η) (2 * s / (V + 1))), by positivity, ?_⟩
  intro r' hr' htc hinfl hclose
  have hcl_s : ∀ t : ℝ, ‖r' t - r₀ t‖ < εs ∧ ‖velocity r' t - velocity r₀ t‖ < εs :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hε1s, lt_of_lt_of_le (hclose t).2.1 hε1s⟩
  have hcl_a : ∀ t : ℝ, ‖r' t - r₀ t‖ < εa ∧ ‖velocity r' t - velocity r₀ t‖ < εa :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hε1a, lt_of_lt_of_le (hclose t).2.1 hε1a⟩
  have hcl_3 : ∀ t : ℝ, ‖r' t - r₀ t‖ < ε₃ ∧ ‖velocity r' t - velocity r₀ t‖ < ε₃ ∧
      ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < ε₃ :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hε13, lt_of_lt_of_le (hclose t).2.1 hε13,
      lt_of_lt_of_le (hclose t).2.2 hε13⟩
  have hcl_w : ∀ t : ℝ, ‖r' t - r₀ t‖ < εw ∧ ‖velocity r' t - velocity r₀ t‖ < εw ∧
      ‖deriv (deriv r') t - deriv (deriv r₀) t‖ < εw :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hε1w, lt_of_lt_of_le (hclose t).2.1 hε1w,
      lt_of_lt_of_le (hclose t).2.2 hε1w⟩
  have hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r' a - knotMap r' b‖ :=
    hsep₀ r' hr' hcl_s
  have hvel' : ∀ t : ℝ, ‖velocity r' t‖ ≤ V + 1 := by
    intro t
    have h1 : ‖velocity r' t‖ ≤ ‖velocity r₀ t‖ + ‖velocity r' t - velocity r₀ t‖ := by
      have h := norm_add_le (velocity r₀ t) (velocity r' t - velocity r₀ t)
      rwa [add_sub_cancel] at h
    have h2 : ‖velocity r' t - velocity r₀ t‖ < 1 := lt_of_lt_of_le (hclose t).2.1 hε11
    have h3 : ‖velocity r₀ t‖ ≤ V := hvel₀ t
    linarith
  have hlip : ∀ a b : KnotParam, ‖knotMap r' a - knotMap r' b‖ ≤ (V + 1) * dist a b :=
    knotMap_lipschitz_of_velocity hr' hvel'
  obtain ⟨t₀, hmax, hslab⟩ := hslab₀ r' hr' hcl_a
  have hslab' : ∀ u : ℝ, FatMiddle r' ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)| := by
    intro u hu k
    have h1 : η ≤ η₀ := by rw [hηdef]; exact min_le_left _ _
    exact lt_of_le_of_lt h1 (hslab u hu k)
  have hnear : ∀ c : ℝ, (∀ t : ℝ, ‖r' t‖ ≤ ‖r' c‖) → ∀ a y u : ℝ, 0 < y → y < period →
      c - ηc ≤ a → a ≤ c + ηc → c - ηc ≤ a + y → a + y ≤ c + ηc →
      a ≤ u → u ≤ a + y → r' u ∉ openSegment ℝ (r' a) (r' (a + y)) :=
    fun c hc a y u hy hyl ha1 ha2 hb1 hb2 hu1 hu2 => hnear₀ r' hr' hcl_3 c hc a y u hy hyl
      ha1 ha2 hb1 hb2 hu1 hu2
  have hwrap : ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δs → a ≤ u → u ≤ a + y →
      r' u ∉ openSegment ℝ (r' a) (r' (a + y)) :=
    fun a y u hy hyl hper hu1 hu2 =>
      hwrap₀ r' hr' hcl_w a y u hy hyl (le_trans hper hδsδw) hu1 hu2
  rcases crosscut_or_spreadQuadS hr' hinfl htc hρ hηpos hηP hmax hslab' hηcpos hηηc hnear
      hδs hδsηc hδsP hwrap hspos (by linarith) hsep hlip with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **`E3′` in the lead's verbatim form `Work.Drive.OFatE3SV`** (with the reference speed bound as a
parameter). -/
theorem ofatE3SV_of_closeS {r₀ : ℝ → Space} (hr₀ : IsSmoothKnot r₀) : OFatE3SV r₀ :=
  fun _ V hVpos hvel₀ => crosscut_or_spreadQuad_of_closeS hr₀ hVpos hvel₀

/-- **Every `E3′` in the verbatim form.** -/
theorem ofatE3SV_all : ∀ r : ℝ → Space, OFatE3SV r :=
  fun r hr => ofatE3SV_of_closeS hr hr

/-- **The speed-bound-free `E3′` (`Work.Drive.OFatE3S`)**, from the verbatim form
(`Work.Drive.ofatE3S_of_V`).  This is the entry point `Work.Drive.spreadCrux_of_endgameS`
consumes. -/
theorem ofatE3S_all : ∀ r : ℝ → Space, OFatE3S r := ofatE3S_of_V ofatE3SV_all

end Work.Drive
