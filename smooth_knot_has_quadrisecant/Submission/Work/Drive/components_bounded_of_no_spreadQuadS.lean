import Mathlib
import Submission.Work.Drive.oFatDefsS
import Submission.Work.Drive.components_bounded_of_no_spreadQuad

namespace Work.Drive


open LeanEval.KnotTheory.Quadrisecant
open Filter Topology
open Classical

set_option maxHeartbeats 1600000

noncomputable section

/-! ## Elementary facts about the `E3′` obstruction set -/

/-- A `ShortMid` point has chord length at most `δs`: the wrap alternative would put a middle on a
chord of length `≥ period - δs`, which `hwrap` forbids. -/
lemma snd_le_of_mem_ShortMid {r : ℝ → Space} {δs : ℝ}
    (hwrap : ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δs → a ≤ u → u ≤ a + y →
      r u ∉ openSegment ℝ (r a) (r (a + y)))
    {q : ℝ × ℝ} (hq : q ∈ ShortMid r δs) : q.2 ≤ δs := by
  obtain ⟨h0, h1, hd, u, hu1, hu2, hu3⟩ := mem_ShortMid_iff.mp hq
  rcases hd with h | h
  · exact h
  · exact absurd hu3 (hwrap q.1 q.2 u h0 h1 h hu1 hu2)

lemma snd_pos_of_mem_OFatObstructionS {r : ℝ → Space} {ρ δs : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ OFatObstructionS r ρ δs) : 0 < q.2 := by
  rcases hq with h | h
  · exact (strip_of_mem_obstruction h).1
  · exact (mem_ShortMid_iff.mp h).1

lemma snd_lt_period_of_mem_OFatObstructionS {r : ℝ → Space} {ρ δs : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ OFatObstructionS r ρ δs) : q.2 < period := by
  rcases hq with h | h
  · exact (strip_of_mem_obstruction h).2
  · exact (mem_ShortMid_iff.mp h).2.1

/-- If `q` lies in `OFatR r ρ ∪ ShortMid r δs` and its chord is short (`q.2 ≤ δs`), then its chord
carries a middle at distance `≤ q.2 ≤ ηc/2` from both endpoints, and `hnear` (applied to the global
maximiser `t₀ + k·period`) forbids the chord's closed arc to meet any slab centre. -/
lemma centre_not_mem_Icc {r : ℝ → Space} (hr : IsSmoothKnot r)
    {ρ δs t₀ ηc : ℝ} (hρ : 0 < ρ) (hηc : 0 < ηc) (hδsηc : δs ≤ ηc / 2)
    (hmax : ∀ t : ℝ, ‖r t‖ ≤ ‖r t₀‖)
    (hnear : ∀ c : ℝ, (∀ t : ℝ, ‖r t‖ ≤ ‖r c‖) → ∀ a y u : ℝ, 0 < y → y < period →
      c - ηc ≤ a → a ≤ c + ηc → c - ηc ≤ a + y → a + y ≤ c + ηc →
      a ≤ u → u ≤ a + y → r u ∉ openSegment ℝ (r a) (r (a + y)))
    {q : ℝ × ℝ} (hq : q ∈ OFatR r ρ ∨ q ∈ ShortMid r δs) (hq2 : q.2 ≤ δs) (k : ℤ) :
    t₀ + (k : ℝ) * period ∉ Set.Icc q.1 (q.1 + q.2) := by
  intro hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have hq0 : 0 < q.2 := by
    rcases hq with h | h
    · exact h.1
    · exact (mem_ShortMid_iff.mp h).1
  have hq1 : q.2 < period := by
    rcases hq with h | h
    · exact h.2.1
    · exact (mem_ShortMid_iff.mp h).2.1
  have hmiddle : ∃ u : ℝ, q.1 ≤ u ∧ u ≤ q.1 + q.2 ∧
      r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := by
    rcases hq with h | h
    · obtain ⟨-, -, u, hu1, hu2, hu3⟩ := h
      exact ⟨u, by linarith [hρ.le], by linarith, hu3⟩
    · exact (mem_ShortMid_iff.mp h).2.2.2
  obtain ⟨u, hu1, hu2, hu3⟩ := hmiddle
  have hc : ∀ t : ℝ, ‖r t‖ ≤ ‖r (t₀ + (k : ℝ) * period)‖ := by
    intro t
    rw [hr.periodic.int_mul k t₀]
    exact hmax t
  refine hnear (t₀ + (k : ℝ) * period) hc q.1 q.2 u hq0 hq1 ?_ ?_ ?_ ?_ hu1 hu2 hu3
  · linarith
  · linarith
  · linarith
  · linarith

/-! ## The cell index of the `E3′` obstruction set -/

/-- The **cell index** of a point of the `E3′` obstruction set: the cell of a fat middle when the
point lies in `OFatR`, and the cell of the arc's parameter midpoint otherwise. -/
noncomputable def kappaS (t₀ : ℝ) (r : ℝ → Space) (ρ : ℝ) (q : ℝ × ℝ) : ℤ :=
  if q ∈ OFatR r ρ then cellAt t₀ r ρ q else cellOf t₀ (q.1 + q.2 / 2)

lemma kappaS_of_mem_OFatR {t₀ : ℝ} {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ OFatR r ρ) : kappaS t₀ r ρ q = cellAt t₀ r ρ q := by
  rw [kappaS, if_pos hq]

lemma kappaS_of_not_mem_OFatR {t₀ : ℝ} {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ}
    (hq : q ∉ OFatR r ρ) : kappaS t₀ r ρ q = cellOf t₀ (q.1 + q.2 / 2) := by
  rw [kappaS, if_neg hq]

/-- If the closed arc `[a,b]` contains no slab centre `t₀ + k·period`, then every point of `[a,b]`
has the same cell index as `a`. -/
lemma cellOf_eq_of_mem_Icc {t₀ a b u : ℝ} (hu : u ∈ Set.Icc a b)
    (hnc : ∀ k : ℤ, t₀ + (k : ℝ) * period ∉ Set.Icc a b) :
    cellOf t₀ u = cellOf t₀ a := by
  have hP : 0 < period := period_pos
  have hja : t₀ + ((cellOf t₀ a : ℤ) : ℝ) * period ≤ a := cellOf_le t₀ a
  have hjb : a < t₀ + (((cellOf t₀ a : ℤ) : ℝ) + 1) * period := cellOf_lt t₀ a
  have hge : cellOf t₀ a ≤ cellOf t₀ u := by
    by_contra hlt
    push_neg at hlt
    have h1 : cellOf t₀ u + 1 ≤ cellOf t₀ a := by omega
    have hcast : ((cellOf t₀ u : ℤ) : ℝ) + 1 ≤ ((cellOf t₀ a : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : t₀ + (((cellOf t₀ u : ℤ) : ℝ) + 1) * period ≤
        t₀ + ((cellOf t₀ a : ℤ) : ℝ) * period := by
      have := mul_le_mul_of_nonneg_right hcast hP.le
      linarith
    have h3 := cellOf_lt t₀ u
    have hu1 : a ≤ u := hu.1
    linarith
  have hle : cellOf t₀ u ≤ cellOf t₀ a := by
    by_contra hlt
    push_neg at hlt
    have h1 : cellOf t₀ a + 1 ≤ cellOf t₀ u := by omega
    have hcast : ((cellOf t₀ a : ℤ) : ℝ) + 1 ≤ ((cellOf t₀ u : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : t₀ + (((cellOf t₀ a : ℤ) : ℝ) + 1) * period ≤
        t₀ + ((cellOf t₀ u : ℤ) : ℝ) * period := by
      have := mul_le_mul_of_nonneg_right hcast hP.le
      linarith
    have h3 := cellOf_le t₀ u
    have h4 : t₀ + (((cellOf t₀ a : ℤ) : ℝ) + 1) * period ∈ Set.Icc a b :=
      ⟨le_of_lt hjb, by linarith [h3, h2, hu.2]⟩
    exact hnc (cellOf t₀ a + 1) (by simpa [Int.cast_add, Int.cast_one] using h4)
  omega

/-- If no slab centre lies in `[a,b]`, then `a` lies strictly to the right of the centre of its own
cell and `b` strictly to the left of the next centre. -/
lemma bounds_of_no_centre {t₀ a b : ℝ} (hab : a ≤ b)
    (hnc : ∀ k : ℤ, t₀ + (k : ℝ) * period ∉ Set.Icc a b) :
    t₀ + (cellOf t₀ a : ℝ) * period < a ∧
      b < t₀ + ((cellOf t₀ a : ℝ) + 1) * period := by
  have hle := cellOf_le t₀ a
  have h1 : t₀ + (cellOf t₀ a : ℝ) * period < a := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      exact hnc (cellOf t₀ a) (h.symm ▸ ⟨le_rfl, hab⟩)
  have h2 : b < t₀ + ((cellOf t₀ a : ℝ) + 1) * period := by
    have h3 : cellOf t₀ b = cellOf t₀ a := cellOf_eq_of_mem_Icc ⟨hab, le_rfl⟩ hnc
    have h4 := cellOf_lt t₀ b
    rwa [h3] at h4
  exact ⟨h1, h2⟩

/-- A point of the obstruction set which is not a limit point of `OFatR ∪ ShortMid` and which is not
in `OFatR` is isolated in the obstruction set: it is a point of `TCset`, the tangent chords are
locally finite, and the other nearby tangent chords can be cut away. -/
lemma exists_isOpen_inter_eq_singleton_of_not_closure {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) {ρ δs : ℝ} {q : ℝ × ℝ}
    (hcl : q ∉ closure (OFatR r ρ ∪ ShortMid r δs))
    (hq : q ∈ OFatObstructionS r ρ δs) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧ U ∩ OFatObstructionS r ρ δs = {q} := by
  obtain ⟨U₂, hU₂o, hqU₂, hU₂fin⟩ := tangentChordLocallyFinite hr hinfl htc q
  have hU₁o : IsOpen (closure (OFatR r ρ ∪ ShortMid r δs))ᶜ := isClosed_closure.isOpen_compl
  have hqU₁ : q ∈ (closure (OFatR r ρ ∪ ShortMid r δs))ᶜ := hcl
  have hFfin : ((TCset r ∩ U₂) \ {q}).Finite := hU₂fin.sdiff
  have hFopen : IsOpen (((TCset r ∩ U₂) \ {q})ᶜ) := hFfin.isClosed.isOpen_compl
  refine ⟨(closure (OFatR r ρ ∪ ShortMid r δs))ᶜ ∩ (U₂ ∩ (((TCset r ∩ U₂) \ {q})ᶜ)), ?_, ?_, ?_⟩
  · exact hU₁o.inter (hU₂o.inter hFopen)
  · exact ⟨hqU₁, hqU₂, fun h => h.2 rfl⟩
  · refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨⟨hxU₁, hxU₂, hxG⟩, hxO⟩
      have hxA : x ∉ OFatR r ρ ∪ ShortMid r δs := fun h => hxU₁ (subset_closure h)
      have hxT : x ∈ TCset r := by
        rcases hxO with h | h
        · rcases h with h | h
          · exact absurd (Or.inl h) hxA
          · exact h
        · exact absurd (Or.inr h) hxA
      have hxF : x ∈ TCset r ∩ U₂ := ⟨hxT, hxU₂⟩
      by_contra hxq
      exact hxG ⟨hxF, by simpa [Set.mem_singleton_iff] using hxq⟩
    · rintro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨⟨hqU₁, hqU₂, fun h => h.2 rfl⟩, hq⟩

/-- The cell (level set of the index `kappaS`) of a point of the obstruction set. -/
def cellSetS (t₀ : ℝ) (r : ℝ → Space) (ρ δs : ℝ) (z : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ OFatObstructionS r ρ δs ∧ kappaS t₀ r ρ q = kappaS t₀ r ρ z}

lemma mem_cellSetS {t₀ : ℝ} {r : ℝ → Space} {ρ δs : ℝ} {z q : ℝ × ℝ} :
    q ∈ cellSetS t₀ r ρ δs z ↔
      q ∈ OFatObstructionS r ρ δs ∧ kappaS t₀ r ρ q = kappaS t₀ r ρ z := Iff.rfl

/-! ## Local constancy of the cell index -/

/-- **The cell index is locally constant on the `E3′` obstruction set** (sequence form): along a
sequence in `OFatObstructionS r ρ δs` converging to a point of it, the index is eventually
constant. -/
lemma kappaS_eventually_eq_of_tendsto {r : ℝ → Space} (hr : IsSmoothKnot r)
    {ρ : ℝ} (hρ : 0 < ρ) {t₀ η : ℝ} (hη : 0 < η)
    (hmax : ∀ t : ℝ, ‖r t‖ ≤ ‖r t₀‖)
    (hslab : ∀ u : ℝ, FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)|)
    {ηc : ℝ} (hηc : 0 < ηc) (hηηc : 2 * η ≤ ηc)
    (hnear : ∀ c : ℝ, (∀ t : ℝ, ‖r t‖ ≤ ‖r c‖) → ∀ a y u : ℝ, 0 < y → y < period →
      c - ηc ≤ a → a ≤ c + ηc → c - ηc ≤ a + y → a + y ≤ c + ηc →
      a ≤ u → u ≤ a + y → r u ∉ openSegment ℝ (r a) (r (a + y)))
    {δs : ℝ} (hδs : 0 < δs) (hδsηc : δs ≤ ηc / 2)
    (hwrap : ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δs → a ≤ u → u ≤ a + y →
      r u ∉ openSegment ℝ (r a) (r (a + y)))
    {s V : ℝ} (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    (hlip : ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ V * dist a b)
    (htc : TangentChordGP r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (hnq : ∀ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w →
      ¬ (IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
         IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)))
    {qs : ℕ → ℝ × ℝ} {q : ℝ × ℝ} (hqs : Tendsto qs atTop (𝓝 q))
    (hqn : ∀ n, qs n ∈ OFatObstructionS r ρ δs) (hq : q ∈ OFatObstructionS r ρ δs) :
    ∀ᶠ n in atTop, kappaS t₀ r ρ (qs n) = kappaS t₀ r ρ q := by
  classical
  have hq0 : 0 < q.2 := snd_pos_of_mem_OFatObstructionS hq
  have hq1 : q.2 < period := snd_lt_period_of_mem_OFatObstructionS hq
  have hqs1 : Tendsto (fun n => (qs n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hqs
  have hqs2 : Tendsto (fun n => (qs n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hqs
  have hqs12 : Tendsto (fun n => (qs n).1 + (qs n).2) atTop (𝓝 (q.1 + q.2)) := hqs1.add hqs2
  by_cases hqO : q ∈ OFatR r ρ
  · by_cases hq2 : q.2 ≤ δs
    · -- #### Case 1: `q ∈ OFatR` with a short chord: its arc is centre-free
      have hnc : ∀ k : ℤ, t₀ + (k : ℝ) * period ∉ Set.Icc q.1 (q.1 + q.2) :=
        centre_not_mem_Icc hr hρ hηc hδsηc hmax hnear (Or.inl hqO) hq2
      have hkq : kappaS t₀ r ρ q = cellOf t₀ q.1 := by
        rw [kappaS_of_mem_OFatR hqO, cellAt]
        exact cellOf_eq_of_mem_Icc
          ⟨by linarith [(midOf_spec (exists_mid_of_mem_OFatR hqO)).1, hρ.le],
           by linarith [(midOf_spec (exists_mid_of_mem_OFatR hqO)).2.1]⟩ hnc
      obtain ⟨hlow, hhigh⟩ := bounds_of_no_centre (le_add_of_nonneg_right hq0.le) hnc
      have hev1 : ∀ᶠ n in atTop, t₀ + (cellOf t₀ q.1 : ℝ) * period < (qs n).1 :=
        (tendsto_order.1 hqs1).1 _ hlow
      have hev2 : ∀ᶠ n in atTop, (qs n).1 + (qs n).2 <
          t₀ + ((cellOf t₀ q.1 : ℝ) + 1) * period :=
        (tendsto_order.1 hqs12).2 _ hhigh
      filter_upwards [hev1, hev2] with n h1 h2
      rw [hkq]
      have hpos : (0 : ℝ) ≤ (qs n).2 := (snd_pos_of_mem_OFatObstructionS (hqn n)).le
      by_cases hnO : qs n ∈ OFatR r ρ
      · rw [kappaS_of_mem_OFatR hnO, cellAt]
        exact cellOf_eq_of_mem
          (by linarith [(midOf_spec (exists_mid_of_mem_OFatR hnO)).1, h1, hρ.le])
          (by linarith [(midOf_spec (exists_mid_of_mem_OFatR hnO)).2.1, h2])
      · rw [kappaS_of_not_mem_OFatR hnO]
        exact cellOf_eq_of_mem (by linarith) (by linarith)
    · -- #### Case 2: `q ∈ OFatR` with a long chord: the original argument
      have hlt : δs < q.2 := lt_of_not_ge hq2
      have hevNotShort : ∀ᶠ n in atTop, qs n ∉ ShortMid r δs := by
        have h2lt : ∀ᶠ n in atTop, δs < (qs n).2 := (tendsto_order.1 hqs2).1 δs hlt
        filter_upwards [h2lt] with n hn hmem
        exact absurd hn (not_lt.mpr (snd_le_of_mem_ShortMid hwrap hmem))
      have hevNotTC : ∀ᶠ n in atTop, qs n ∉ TCset r \ OFatR r ρ := by
        by_contra hcon
        rw [Filter.not_eventually] at hcon
        obtain ⟨φ, hφ, hφT⟩ := Filter.extraction_of_frequently_atTop hcon
        have hlim : Tendsto (fun n => qs (φ n)) atTop (𝓝 q) := hqs.comp hφ.tendsto_atTop
        have hcl : q ∈ closure (TCset r \ OFatR r ρ) :=
          mem_closure_iff_seq_limit.mpr ⟨fun n => qs (φ n), fun n => not_not.mp (hφT n), hlim⟩
        exact ((isClosed_TCset_sdiff_OFatR hr hinfl htc ρ).closure_subset hcl).2 hqO
      have hevO : ∀ᶠ n in atTop, qs n ∈ OFatR r ρ := by
        filter_upwards [hevNotShort, hevNotTC] with n h1 h2
        rcases hqn n with h | h
        · rcases h with h | h
          · exact h
          · by_contra hno
            exact h2 ⟨h, hno⟩
        · exact absurd h h1
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevO
      have hcell := cellAt_eventually_eq_of_tendsto hr hρ hη hslab hs hV hsep hlip hnq
        (qs := fun k => qs (k + N)) (q := q) (hqs.comp (tendsto_add_atTop_nat N))
        (fun k => hN (k + N) (by omega)) hqO
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hcell
      refine Filter.eventually_atTop.mpr ⟨M + N, fun n hn => ?_⟩
      have hNn : N ≤ n := by omega
      have hge : M ≤ n - N := by omega
      have h1 : cellAt t₀ r ρ (qs (n - N + N)) = cellAt t₀ r ρ q := hM (n - N) hge
      rw [Nat.sub_add_cancel hNn] at h1
      rw [kappaS_of_mem_OFatR (hN n (by omega)), h1, ← kappaS_of_mem_OFatR hqO]
  · -- #### Case 3: `q ∉ OFatR`
    have hkq : kappaS t₀ r ρ q = cellOf t₀ (q.1 + q.2 / 2) := kappaS_of_not_mem_OFatR hqO
    have hevNotO : ∀ᶠ n in atTop, qs n ∉ OFatR r ρ := by
      by_contra hcon
      rw [Filter.not_eventually] at hcon
      obtain ⟨φ, hφ, hφO⟩ := Filter.extraction_of_frequently_atTop hcon
      have hlim : Tendsto (fun n => qs (φ n)) atTop (𝓝 q) := hqs.comp hφ.tendsto_atTop
      have hcl : q ∈ closure (OFatR r ρ) :=
        mem_closure_iff_seq_limit.mpr ⟨fun n => qs (φ n), fun n => not_not.mp (hφO n), hlim⟩
      exact hqO (closure_OFatR_subset_of_strip hr hρ hcl hq0 hq1)
    by_cases hcs : ∃ k : ℤ, q.1 + q.2 / 2 = t₀ + (k : ℝ) * period
    · -- the arc's midpoint is a global maximiser: `q` is isolated
      have hnotcl : q ∉ closure (OFatR r ρ ∪ ShortMid r δs) := by
        intro hcl
        have hclS : q ∈ closure (ShortMid r δs) := by
          rw [closure_union] at hcl
          rcases hcl with h | h
          · exact absurd (closure_OFatR_subset_of_strip hr hρ h hq0 hq1) hqO
          · exact h
        obtain ⟨qm, hqm, hqmt⟩ := mem_closure_iff_seq_limit.mp hclS
        obtain ⟨k, hk⟩ := hcs
        have hqm1 : Tendsto (fun m => (qm m).1) atTop (𝓝 q.1) :=
          (continuous_fst.tendsto q).comp hqmt
        have hqm12 : Tendsto (fun m => (qm m).1 + (qm m).2) atTop (𝓝 (q.1 + q.2)) :=
          hqm1.add ((continuous_snd.tendsto q).comp hqmt)
        have ha : ∀ᶠ m in atTop, (qm m).1 < t₀ + (k : ℝ) * period :=
          (tendsto_order.1 hqm1).2 _ (by linarith [hk])
        have hb : ∀ᶠ m in atTop, t₀ + (k : ℝ) * period < (qm m).1 + (qm m).2 :=
          (tendsto_order.1 hqm12).1 _ (by linarith [hk])
        obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp (ha.and hb)
        exact centre_not_mem_Icc hr hρ hηc hδsηc hmax hnear (Or.inr (hqm m))
          (snd_le_of_mem_ShortMid hwrap (hqm m)) k
          ⟨le_of_lt (hm m le_rfl).1, le_of_lt (hm m le_rfl).2⟩
      obtain ⟨U, hUo, hqU, hUeq⟩ :=
        exists_isOpen_inter_eq_singleton_of_not_closure hr hinfl htc hnotcl hq
      filter_upwards [hqs.eventually (hUo.mem_nhds hqU)] with n hn
      have hmem : qs n ∈ U ∩ OFatObstructionS r ρ δs := ⟨hn, hqn n⟩
      rw [hUeq] at hmem
      rw [Set.mem_singleton_iff.mp hmem]
    · -- the arc's midpoint is not a maximiser: continuity
      have hsnot : q.1 + q.2 / 2 ≠ t₀ + (cellOf t₀ (q.1 + q.2 / 2) : ℝ) * period := by
        intro h
        exact hcs ⟨cellOf t₀ (q.1 + q.2 / 2), h⟩
      have hlow : t₀ + (cellOf t₀ (q.1 + q.2 / 2) : ℝ) * period < q.1 + q.2 / 2 := by
        rcases lt_or_eq_of_le (cellOf_le t₀ (q.1 + q.2 / 2)) with h | h
        · exact h
        · exact absurd h.symm hsnot
      have hhigh : q.1 + q.2 / 2 < t₀ + ((cellOf t₀ (q.1 + q.2 / 2) : ℝ) + 1) * period :=
        cellOf_lt t₀ (q.1 + q.2 / 2)
      have hscont : Tendsto (fun n => (qs n).1 + (qs n).2 / 2) atTop (𝓝 (q.1 + q.2 / 2)) :=
        hqs1.add (hqs2.div_const 2)
      have hev1 : ∀ᶠ n in atTop,
          t₀ + (cellOf t₀ (q.1 + q.2 / 2) : ℝ) * period < (qs n).1 + (qs n).2 / 2 :=
        (tendsto_order.1 hscont).1 _ hlow
      have hev2 : ∀ᶠ n in atTop,
          (qs n).1 + (qs n).2 / 2 < t₀ + ((cellOf t₀ (q.1 + q.2 / 2) : ℝ) + 1) * period :=
        (tendsto_order.1 hscont).2 _ hhigh
      filter_upwards [hev1, hev2, hevNotO] with n h1 h2 hnO
      rw [hkq, kappaS_of_not_mem_OFatR hnO]
      exact cellOf_eq_of_mem (le_of_lt h1) h2

/-- **All components of the `E3′` obstruction set are bounded in the strip coordinate** (the
corrected form of the lead's `NOTES_LEAD_E3prime_wrap.md` §4: the WIP signature of
`components_bounded_of_no_spreadQuadS` with the extra wrap-freeness hypothesis `hwrap` inserted after
`hδsηc`). -/
theorem components_bounded_of_no_spreadQuadS
    {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    {t₀ η : ℝ} (hη : 0 < η) (hηP : 2 * η < period)
    (hmax : ∀ t : ℝ, ‖r t‖ ≤ ‖r t₀‖)
    (hslab : ∀ u : ℝ, FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)|)
    {ηc : ℝ} (hηc : 0 < ηc) (hηηc : 2 * η ≤ ηc)
    (hnear : ∀ c : ℝ, (∀ t : ℝ, ‖r t‖ ≤ ‖r c‖) → ∀ a y u : ℝ, 0 < y → y < period →
      c - ηc ≤ a → a ≤ c + ηc → c - ηc ≤ a + y → a + y ≤ c + ηc →
      a ≤ u → u ≤ a + y → r u ∉ openSegment ℝ (r a) (r (a + y)))
    {δs : ℝ} (hδs : 0 < δs) (hδsηc : δs ≤ ηc / 2)
    (hwrap : ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δs → a ≤ u → u ≤ a + y →
      r u ∉ openSegment ℝ (r a) (r (a + y)))
    {s V : ℝ} (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    (hlip : ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ V * dist a b)
    (htc : TangentChordGP r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (hnq : ∀ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w →
      ¬ (IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
         IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam))) :
    ∀ z : ℝ × ℝ, z ∈ OFatObstructionS r ρ δs →
      Bornology.IsBounded (Prod.fst '' connectedComponentIn (OFatObstructionS r ρ δs) z) := by
  intro z hz
  classical
  have hloc : ∀ {qs : ℕ → ℝ × ℝ} {q : ℝ × ℝ}, Tendsto qs atTop (𝓝 q) →
      (∀ n, qs n ∈ OFatObstructionS r ρ δs) → q ∈ OFatObstructionS r ρ δs →
      ∀ᶠ n in atTop, kappaS t₀ r ρ (qs n) = kappaS t₀ r ρ q :=
    fun hqs hqn hq => kappaS_eventually_eq_of_tendsto hr hρ hη hmax hslab hηc hηηc hnear
      hδs hδsηc hwrap hs hV hsep hlip htc hinfl hnq hqs hqn hq
  have hzS : z ∈ cellSetS t₀ r ρ δs z := ⟨hz, rfl⟩
  have hcl₁ : closure (cellSetS t₀ r ρ δs z) ∩ OFatObstructionS r ρ δs ⊆
      cellSetS t₀ r ρ δs z := by
    rintro q ⟨hqcl, hqA⟩
    obtain ⟨qs, hqs_mem, hqs⟩ := mem_closure_iff_seq_limit.mp hqcl
    have hev := hloc hqs (fun n => (hqs_mem n).1) hqA
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨hqA, ?_⟩
    rw [← hN N le_rfl]
    exact (hqs_mem N).2
  have hcl₂ : closure (OFatObstructionS r ρ δs \ cellSetS t₀ r ρ δs z) ∩
      OFatObstructionS r ρ δs ⊆ OFatObstructionS r ρ δs \ cellSetS t₀ r ρ δs z := by
    rintro q ⟨hqcl, hqA⟩
    obtain ⟨qs, hqs_mem, hqs⟩ := mem_closure_iff_seq_limit.mp hqcl
    have hev := hloc hqs (fun n => (hqs_mem n).1) hqA
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨hqA, ?_⟩
    rintro hqS
    have hbad : kappaS t₀ r ρ (qs N) = kappaS t₀ r ρ z := by
      rw [hN N le_rfl]
      exact hqS.2
    exact (hqs_mem N).2 ⟨(hqs_mem N).1, hbad⟩
  have hA_sub : OFatObstructionS r ρ δs ⊆ closure (cellSetS t₀ r ρ δs z) ∪
      closure (OFatObstructionS r ρ δs \ cellSetS t₀ r ρ δs z) := by
    intro x hx
    by_cases hxS : x ∈ cellSetS t₀ r ρ δs z
    · exact Or.inl (subset_closure hxS)
    · exact Or.inr (subset_closure ⟨hx, hxS⟩)
  have hdisj : connectedComponentIn (OFatObstructionS r ρ δs) z ∩
      (closure (cellSetS t₀ r ρ δs z) ∩
        closure (OFatObstructionS r ρ δs \ cellSetS t₀ r ρ δs z)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxK, hxScl, hxDScl⟩
    have hxA := connectedComponentIn_subset _ _ hxK
    exact (hcl₂ ⟨hxDScl, hxA⟩).2 (hcl₁ ⟨hxScl, hxA⟩)
  have hKsub : connectedComponentIn (OFatObstructionS r ρ δs) z ⊆ cellSetS t₀ r ρ δs z := by
    have hzK : z ∈ connectedComponentIn (OFatObstructionS r ρ δs) z := mem_connectedComponentIn hz
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      isPreconnected_connectedComponentIn (closure (cellSetS t₀ r ρ δs z))
      (closure (OFatObstructionS r ρ δs \ cellSetS t₀ r ρ δs z)) isClosed_closure
      isClosed_closure
      (fun x hx => hA_sub (connectedComponentIn_subset _ _ hx)) hdisj) with h | h
    · exact fun x hx => hcl₁ ⟨h hx, connectedComponentIn_subset _ _ hx⟩
    · exact absurd hzS (hcl₂ ⟨h hzK, hz⟩).2
  refine Bornology.IsBounded.subset (Metric.isBounded_Icc
    (t₀ + (kappaS t₀ r ρ z : ℝ) * period - period)
    (t₀ + ((kappaS t₀ r ρ z : ℝ) + 1) * period)) ?_
  rintro x ⟨q, hqK, rfl⟩
  have hqS := hKsub hqK
  have hqO : q ∈ OFatObstructionS r ρ δs := hqS.1
  have hqk : kappaS t₀ r ρ q = kappaS t₀ r ρ z := hqS.2
  have hq2 : q.2 < period := snd_lt_period_of_mem_OFatObstructionS hqO
  by_cases hqO' : q ∈ OFatR r ρ
  · have hmid := midOf_spec (exists_mid_of_mem_OFatR hqO')
    have hcell : cellOf t₀ (midOf r ρ q) = kappaS t₀ r ρ z := by
      rw [← hqk, kappaS_of_mem_OFatR hqO', cellAt]
    have hc := cellOf_eq_iff.mp hcell
    constructor
    · linarith [hmid.1, hmid.2.1, hc.1, hq2]
    · linarith [hmid.1, hc.2, hρ.le]
  · have hcell : cellOf t₀ (q.1 + q.2 / 2) = kappaS t₀ r ρ z := by
      rw [← hqk, kappaS_of_not_mem_OFatR hqO']
    have hc := cellOf_eq_iff.mp hcell
    have hq0 : 0 < q.2 := snd_pos_of_mem_OFatObstructionS hqO
    constructor
    · linarith [hc.1, hq2]
    · linarith [hc.2, hq0]


end

end Work.Drive
