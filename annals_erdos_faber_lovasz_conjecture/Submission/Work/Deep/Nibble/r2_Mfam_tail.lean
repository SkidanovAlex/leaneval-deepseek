import Submission.Work.Deep.Nibble.FamWaste

/-!
# The matched-coverage tail bound of one wasteful round

This module proves `Work.Deep.Nibble.r2_Mfam_tail`, the concentration of the
number `matchedFam 𝓖 ω S` of vertices of `S` covered by an *isolated* kept edge
of one round, around its mean, with certificate size `4 D |S|` (Bruhn--Joos /
Talagrand, `Work.Deep.Nibble.bj_talagrand`).

The certificate of an outcome `ω` is the union of the edges through the vertices
of `S` together with one chosen blocker of every *kept* edge through `S`; a
blocker of a kept edge `e` is a kept edge meeting `e`.  A vertex becomes newly
matched between `ω` and `ω'` either because its witness edge is kept in `ω'` but
not in `ω` (a disagreement on an edge through `S`) or because every blocker of
its (kept) witness is unkept in `ω'`, in which case the chosen blocker is itself
a disagreement.  A single blocker serves at most `r` newly isolated edges (they
are pairwise disjoint and all meet it) and each of them contributes at most `r`
vertices, whence the factor `r²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The isolated coverage -/

/-- The vertices covered by an isolated kept edge of the round. -/
def isoCov (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) : Set V := ⋃ e ∈ isoFam 𝓖 ω, (e : Set V)

@[simp] lemma mem_isoCov {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {v : V} :
    v ∈ isoCov 𝓖 ω ↔ ∃ e : 𝓖, e ∈ isoFam 𝓖 ω ∧ v ∈ (e : Set V) := by
  unfold isoCov
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨e, he⟩
    rw [Set.mem_iUnion] at he
    exact ⟨e, he.1, he.2⟩
  · rintro ⟨e, he, hve⟩
    exact ⟨e, Set.mem_iUnion.mpr ⟨he, hve⟩⟩

lemma matchedFam_eq_isoCov_card (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    matchedFam 𝓖 ω S = (S.filter (fun v => v ∈ isoCov 𝓖 ω)).card := by
  rw [matchedFam]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro v _
  simp only [isoCov]

lemma matchedFam_le_card (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    matchedFam 𝓖 ω S ≤ S.card := by
  rw [matchedFam_eq_isoCov_card]
  exact Finset.card_filter_le _ _

/-! ## Witnesses and blockers -/

/-- An isolated kept edge of `ω` through `v` (junk if `v` is not covered). -/
noncomputable def witIso (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e₀ : 𝓖) (v : V) : 𝓖 := by
  classical
  exact if h : ∃ e : 𝓖, e ∈ isoFam 𝓖 ω ∧ v ∈ (e : Set V) then Classical.choose h else e₀

lemma witIso_spec {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {e₀ : 𝓖} {v : V}
    (h : ∃ e : 𝓖, e ∈ isoFam 𝓖 ω ∧ v ∈ (e : Set V)) :
    witIso 𝓖 ω e₀ v ∈ isoFam 𝓖 ω ∧ v ∈ (witIso 𝓖 ω e₀ v : Set V) := by
  rw [witIso, dif_pos h]
  exact Classical.choose_spec h

/-- A blocker of a kept edge: a kept edge meeting it (junk if there is none). -/
noncomputable def blockerOf (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e : 𝓖) : 𝓖 := by
  classical
  exact if h : ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ ((f : Set V) ∩ (e : Set V)).Nonempty
    then Classical.choose h else e

lemma blockerOf_spec (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e : 𝓖)
    (h : ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ ((f : Set V) ∩ (e : Set V)).Nonempty) :
    blockerOf 𝓖 ω e ≠ e ∧ ω (blockerOf 𝓖 ω e) = true ∧
      ((blockerOf 𝓖 ω e : Set V) ∩ (e : Set V)).Nonempty := by
  rw [blockerOf, dif_pos h]
  exact Classical.choose_spec h

/-- A kept edge that is not isolated has a blocker. -/
lemma exists_blocker (𝓖 : Set (Set V)) {ω : 𝓖 → Bool} {e : 𝓖} (hkept : ω e = true)
    (hnot : e ∉ isoFam 𝓖 ω) :
    ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ ((f : Set V) ∩ (e : Set V)).Nonempty := by
  by_contra hc
  exact hnot ⟨hkept, fun f hfe hf => eq_false (fun hme => hc ⟨f, hfe, hf, hme⟩)⟩

/-- The blocker of a kept edge is unkept in `ω'` as soon as the edge is isolated in `ω'`. -/
lemma blockerOf_eq_false_of_mem_iso (𝓖 : Set (Set V)) {ω ω' : 𝓖 → Bool} {e : 𝓖}
    (hiso : e ∈ isoFam 𝓖 ω')
    (hex : ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ ((f : Set V) ∩ (e : Set V)).Nonempty) :
    ω' (blockerOf 𝓖 ω e) = false := by
  obtain ⟨hne, -, hmeet⟩ := blockerOf_spec 𝓖 ω e hex
  by_contra hc
  have hc' : ω' (blockerOf 𝓖 ω e) = true := by
    rcases Bool.eq_false_or_eq_true (ω' (blockerOf 𝓖 ω e)) with h | h
    · exact h
    · exact absurd h hc
  have h1 := hiso.2 (blockerOf 𝓖 ω e) hne hc'
  rw [h1] at hmeet
  exact hmeet

/-! ## The certificate set and the vertex sets of the counting -/

/-- The coordinate set certifying the matched coverage: the edges through the
vertices of `S`, together with one chosen blocker of every kept such edge. -/
noncomputable def certM (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : Finset 𝓖 := by
  classical
  exact (S.biUnion (fun v => thruF 𝓖 v)) ∪
    (((S.biUnion (fun v => thruF 𝓖 v)).filter (fun e => ω e = true)).image (blockerOf 𝓖 ω))

/-- The disagreements between `ω` and `ω'` inside the certificate. -/
noncomputable def disJV (𝓖 : Set (Set V)) (ω ω' : 𝓖 → Bool) (S : Finset V) : Finset 𝓖 := by
  classical
  exact (certM 𝓖 ω S).filter (fun e => ω e ≠ ω' e)

/-- The disagreements where `ω` did not keep the edge. -/
noncomputable def disOnV (𝓖 : Set (Set V)) (ω ω' : 𝓖 → Bool) (S : Finset V) : Finset 𝓖 := by
  classical
  exact (disJV 𝓖 ω ω' S).filter (fun e => ω e = false)

/-- The disagreements where `ω` kept the edge. -/
noncomputable def disOffV (𝓖 : Set (Set V)) (ω ω' : 𝓖 → Bool) (S : Finset V) : Finset 𝓖 := by
  classical
  exact (disJV 𝓖 ω ω' S).filter (fun e => ω e = true)

/-- The vertices of `S` newly matched when passing from `ω` to `ω'`. -/
noncomputable def newVFam (𝓖 : Set (Set V)) (ω ω' : 𝓖 → Bool) (S : Finset V) : Finset V := by
  classical
  exact S.filter (fun v => v ∈ isoCov 𝓖 ω' ∧ v ∉ isoCov 𝓖 ω)

/-- The newly matched vertices whose witness is unkept in `ω`. -/
noncomputable def newAV (𝓖 : Set (Set V)) (ω ω' : 𝓖 → Bool) (e₀ : 𝓖) (S : Finset V) : Finset V := by
  classical
  exact (newVFam 𝓖 ω ω' S).filter (fun v => ω (witIso 𝓖 ω' e₀ v) = false)

/-- The newly matched vertices whose witness is kept in `ω`. -/
noncomputable def newBV (𝓖 : Set (Set V)) (ω ω' : 𝓖 → Bool) (e₀ : 𝓖) (S : Finset V) : Finset V := by
  classical
  exact (newVFam 𝓖 ω ω' S).filter (fun v => ω (witIso 𝓖 ω' e₀ v) = true)

@[simp] lemma mem_certM {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {S : Finset V} {e : 𝓖} :
    e ∈ certM 𝓖 ω S ↔ e ∈ S.biUnion (fun v => thruF 𝓖 v) ∨
      e ∈ ((S.biUnion (fun v => thruF 𝓖 v)).filter (fun e => ω e = true)).image (blockerOf 𝓖 ω) := by
  rw [certM, Finset.mem_union]

@[simp] lemma mem_disJV {𝓖 : Set (Set V)} {ω ω' : 𝓖 → Bool} {S : Finset V} {e : 𝓖} :
    e ∈ disJV 𝓖 ω ω' S ↔ e ∈ certM 𝓖 ω S ∧ ω e ≠ ω' e := by
  rw [disJV, Finset.mem_filter]

@[simp] lemma mem_disOnV {𝓖 : Set (Set V)} {ω ω' : 𝓖 → Bool} {S : Finset V} {e : 𝓖} :
    e ∈ disOnV 𝓖 ω ω' S ↔ e ∈ disJV 𝓖 ω ω' S ∧ ω e = false := by
  rw [disOnV, Finset.mem_filter]

@[simp] lemma mem_disOffV {𝓖 : Set (Set V)} {ω ω' : 𝓖 → Bool} {S : Finset V} {e : 𝓖} :
    e ∈ disOffV 𝓖 ω ω' S ↔ e ∈ disJV 𝓖 ω ω' S ∧ ω e = true := by
  rw [disOffV, Finset.mem_filter]

@[simp] lemma mem_newVFam {𝓖 : Set (Set V)} {ω ω' : 𝓖 → Bool} {S : Finset V} {v : V} :
    v ∈ newVFam 𝓖 ω ω' S ↔ v ∈ S ∧ v ∈ isoCov 𝓖 ω' ∧ v ∉ isoCov 𝓖 ω := by
  rw [newVFam, Finset.mem_filter]

@[simp] lemma mem_newAV {𝓖 : Set (Set V)} {ω ω' : 𝓖 → Bool} {e₀ : 𝓖} {S : Finset V} {v : V} :
    v ∈ newAV 𝓖 ω ω' e₀ S ↔ v ∈ newVFam 𝓖 ω ω' S ∧ ω (witIso 𝓖 ω' e₀ v) = false := by
  rw [newAV, Finset.mem_filter]

@[simp] lemma mem_newBV {𝓖 : Set (Set V)} {ω ω' : 𝓖 → Bool} {e₀ : 𝓖} {S : Finset V} {v : V} :
    v ∈ newBV 𝓖 ω ω' e₀ S ↔ v ∈ newVFam 𝓖 ω ω' S ∧ ω (witIso 𝓖 ω' e₀ v) = true := by
  rw [newBV, Finset.mem_filter]

/-! ## Small counting lemmas -/

/-- `r` pairwise disjoint edges meeting a fixed edge: there are at most `r`. -/
lemma card_le_eFin_card_of_pairwiseDisjoint_meets {𝓖 : Set (Set V)} {r : ℕ} (huni : HUnif 𝓖 r)
    {W : Finset 𝓖} {i : 𝓖}
    (hdisj : ∀ e ∈ W, ∀ f ∈ W, e ≠ f → Disjoint (e : Set V) (f : Set V))
    (hmeet : ∀ e ∈ W, ((e : Set V) ∩ (i : Set V)).Nonempty) : W.card ≤ r := by
  classical
  have hone : ∀ e ∈ W, 1 ≤ (eFin 𝓖 e ∩ eFin 𝓖 i).card := by
    intro e he
    obtain ⟨x, hx1, hx2⟩ := hmeet e he
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr
      ⟨(eFin_mem_iff 𝓖).mpr hx1, (eFin_mem_iff 𝓖).mpr hx2⟩⟩
  have h1 : W.card ≤ ∑ e ∈ W, (eFin 𝓖 e ∩ eFin 𝓖 i).card := by
    calc W.card = ∑ e ∈ W, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ e ∈ W, (eFin 𝓖 e ∩ eFin 𝓖 i).card := Finset.sum_le_sum hone
  have hpd : (W : Set 𝓖).PairwiseDisjoint (fun e => eFin 𝓖 e ∩ eFin 𝓖 i) := by
    intro e he f hf hef
    refine Finset.disjoint_left.mpr ?_
    intro x hxe hxf
    have hd := hdisj e he f hf hef
    exact (Set.disjoint_left.mp hd) ((eFin_mem_iff 𝓖).mp (Finset.mem_inter.mp hxe).1)
      ((eFin_mem_iff 𝓖).mp (Finset.mem_inter.mp hxf).1)
  have h2 : ∑ e ∈ W, (eFin 𝓖 e ∩ eFin 𝓖 i).card =
      (W.biUnion (fun e => eFin 𝓖 e ∩ eFin 𝓖 i)).card :=
    (Finset.card_biUnion hpd).symm
  have h3 : W.biUnion (fun e => eFin 𝓖 e ∩ eFin 𝓖 i) ⊆ eFin 𝓖 i := by
    intro x hx
    obtain ⟨e, -, hxe⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxe).2
  calc W.card ≤ ∑ e ∈ W, (eFin 𝓖 e ∩ eFin 𝓖 i).card := h1
    _ = (W.biUnion (fun e => eFin 𝓖 e ∩ eFin 𝓖 i)).card := h2
    _ ≤ (eFin 𝓖 i).card := Finset.card_le_card h3
    _ = r := eFin_card_of_hunif huni i

/-- The certificate has at most `2 D |S|` edges through `S` and at most `2 D |S|`
blockers. -/
lemma certM_card_le (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) {D : ℕ}
    (hdeg : ∀ v : V, ((hd 𝓖 v : ℝ)) ≤ 2 * (D : ℝ)) :
    (certM 𝓖 ω S).card ≤ 4 * D * S.card := by
  classical
  have hthru : ∀ v : V, (thruF 𝓖 v).card ≤ 2 * D := by
    intro v
    have h := hdeg v
    rw [hd_eq_card_thruF 𝓖 v] at h
    exact_mod_cast h
  have h1 : (S.biUnion (fun v => thruF 𝓖 v)).card ≤ 2 * D * S.card := by
    calc (S.biUnion (fun v => thruF 𝓖 v)).card ≤ ∑ v ∈ S, (thruF 𝓖 v).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ v ∈ S, 2 * D := Finset.sum_le_sum (fun v _ => hthru v)
      _ = 2 * D * S.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have h2 : (((S.biUnion (fun v => thruF 𝓖 v)).filter (fun e => ω e = true)).image
      (blockerOf 𝓖 ω)).card ≤ 2 * D * S.card := by
    calc _ ≤ ((S.biUnion (fun v => thruF 𝓖 v)).filter (fun e => ω e = true)).card :=
          Finset.card_image_le
      _ ≤ (S.biUnion (fun v => thruF 𝓖 v)).card := Finset.card_filter_le _ _
      _ ≤ 2 * D * S.card := h1
  rw [certM]
  calc ((S.biUnion (fun v => thruF 𝓖 v)) ∪
        ((S.biUnion (fun v => thruF 𝓖 v)).filter (fun e => ω e = true)).image (blockerOf 𝓖 ω)).card
      ≤ (S.biUnion (fun v => thruF 𝓖 v)).card
        + (((S.biUnion (fun v => thruF 𝓖 v)).filter (fun e => ω e = true)).image
            (blockerOf 𝓖 ω)).card := Finset.card_union_le _ _
    _ ≤ 2 * D * S.card + 2 * D * S.card := Nat.add_le_add h1 h2
    _ = 4 * D * S.card := by ring

/-! ## The certificate inequality -/

lemma matchedFam_lt_add_of_card_lt {𝓖 : Set (Set V)} {r : ℕ} (hr : 1 ≤ r) (huni : HUnif 𝓖 r)
    (e₀ : 𝓖) (S : Finset V) (ω ω' : 𝓖 → Bool) {u : ℝ}
    (hcard : ((disJV 𝓖 ω ω' S).card : ℝ) < u / (r : ℝ) ^ 2) :
    ((matchedFam 𝓖 ω' S : ℕ) : ℝ) < ((matchedFam 𝓖 ω S : ℕ) : ℝ) + u := by
  classical
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hu : 0 < u := by
    have h1 : (0:ℝ) ≤ ((disJV 𝓖 ω ω' S).card : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) < u / (r:ℝ)^2 := lt_of_le_of_lt h1 hcard
    have h3 : (0:ℝ) < (r:ℝ)^2 := by positivity
    by_contra hcon
    push_neg at hcon
    have h4 : u / (r:ℝ)^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon h3.le
    linarith
  rcases Nat.eq_zero_or_pos S.card with hS | hSpos
  · have hz : ∀ ω : 𝓖 → Bool, matchedFam 𝓖 ω S = 0 := by
      intro ω
      rw [matchedFam_eq_isoCov_card 𝓖 ω S, Finset.card_eq_zero.mp hS]
      simp
    rw [hz ω', hz ω]
    simp only [Nat.cast_zero]
    linarith
  · have hwit : ∀ v ∈ newVFam 𝓖 ω ω' S,
        witIso 𝓖 ω' e₀ v ∈ isoFam 𝓖 ω' ∧ v ∈ (witIso 𝓖 ω' e₀ v : Set V) := by
      intro v hv
      exact witIso_spec (mem_isoCov.mp (mem_newVFam.mp hv).2.1)
    have hwit_thru : ∀ v ∈ newVFam 𝓖 ω ω' S,
        witIso 𝓖 ω' e₀ v ∈ S.biUnion (fun v => thruF 𝓖 v) := by
      intro v hv
      have hvS : v ∈ S := (mem_newVFam.mp hv).1
      have hth : witIso 𝓖 ω' e₀ v ∈ thruF 𝓖 v := (mem_thruF 𝓖).mpr (hwit v hv).2
      exact Finset.mem_biUnion.mpr ⟨v, hvS, hth⟩
    have hwit_cert : ∀ v ∈ newVFam 𝓖 ω ω' S, witIso 𝓖 ω' e₀ v ∈ certM 𝓖 ω S := by
      intro v hv
      rw [mem_certM]
      exact Or.inl (hwit_thru v hv)
    have hstep1 : matchedFam 𝓖 ω' S ≤ matchedFam 𝓖 ω S + (newVFam 𝓖 ω ω' S).card := by
      rw [matchedFam_eq_isoCov_card 𝓖 ω' S, matchedFam_eq_isoCov_card 𝓖 ω S]
      have hsub : S.filter (fun v => v ∈ isoCov 𝓖 ω') ⊆
          (S.filter (fun v => v ∈ isoCov 𝓖 ω)) ∪ newVFam 𝓖 ω ω' S := by
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨hvS, hv'⟩ := hv
        by_cases h : v ∈ isoCov 𝓖 ω
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hvS, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (by simp [hvS, hv', h]))
      calc (S.filter (fun v => v ∈ isoCov 𝓖 ω')).card
          ≤ ((S.filter (fun v => v ∈ isoCov 𝓖 ω)) ∪ newVFam 𝓖 ω ω' S).card :=
            Finset.card_le_card hsub
        _ ≤ (S.filter (fun v => v ∈ isoCov 𝓖 ω)).card + (newVFam 𝓖 ω ω' S).card :=
            Finset.card_union_le _ _
    have hstep2 : (newVFam 𝓖 ω ω' S).card ≤
        (newAV 𝓖 ω ω' e₀ S).card + (newBV 𝓖 ω ω' e₀ S).card := by
      have hsub : newVFam 𝓖 ω ω' S ⊆ newAV 𝓖 ω ω' e₀ S ∪ newBV 𝓖 ω ω' e₀ S := by
        intro v hv
        rcases Bool.eq_false_or_eq_true (ω (witIso 𝓖 ω' e₀ v)) with h | h
        · exact Finset.mem_union.mpr (Or.inr (by simp [hv, h]))
        · exact Finset.mem_union.mpr (Or.inl (by simp [hv, h]))
      calc (newVFam 𝓖 ω ω' S).card ≤ (newAV 𝓖 ω ω' e₀ S ∪ newBV 𝓖 ω ω' e₀ S).card :=
            Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
    have hfibA : ∀ i ∈ disOnV 𝓖 ω ω' S,
        ((newAV 𝓖 ω ω' e₀ S).filter (fun v => witIso 𝓖 ω' e₀ v = i)).card ≤ r := by
      intro i hi
      have hle : (newAV 𝓖 ω ω' e₀ S).filter (fun v => witIso 𝓖 ω' e₀ v = i) ⊆ eFin 𝓖 i := by
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨hvA, hwi⟩ := hv
        have hvV : v ∈ newVFam 𝓖 ω ω' S := (mem_newAV.mp hvA).1
        have hmem : v ∈ (witIso 𝓖 ω' e₀ v : Set V) := (hwit v hvV).2
        rw [hwi] at hmem
        exact (eFin_mem_iff 𝓖).mpr hmem
      calc ((newAV 𝓖 ω ω' e₀ S).filter (fun v => witIso 𝓖 ω' e₀ v = i)).card
          ≤ (eFin 𝓖 i).card := Finset.card_le_card hle
        _ = r := eFin_card_of_hunif huni i
    have hstep3a : (newAV 𝓖 ω ω' e₀ S).card ≤ (disOnV 𝓖 ω ω' S).card * r := by
      have hmaps : Set.MapsTo (witIso 𝓖 ω' e₀) ↑(newAV 𝓖 ω ω' e₀ S) ↑(disOnV 𝓖 ω ω' S) := by
        intro v hv
        obtain ⟨hvV, hfalse⟩ := mem_newAV.mp hv
        have hiso := hwit v hvV
        refine Finset.mem_filter.mpr ⟨?_, hfalse⟩
        refine Finset.mem_filter.mpr ⟨hwit_cert v hvV, ?_⟩
        rw [hfalse, hiso.1.1]
        simp
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      calc ∑ i ∈ disOnV 𝓖 ω ω' S,
            ((newAV 𝓖 ω ω' e₀ S).filter (fun v => witIso 𝓖 ω' e₀ v = i)).card
          ≤ ∑ i ∈ disOnV 𝓖 ω ω' S, r := Finset.sum_le_sum hfibA
        _ = (disOnV 𝓖 ω ω' S).card * r := by rw [Finset.sum_const, smul_eq_mul]
    have hblk_notiso : ∀ v ∈ newVFam 𝓖 ω ω' S, ω (witIso 𝓖 ω' e₀ v) = true →
        witIso 𝓖 ω' e₀ v ∉ isoFam 𝓖 ω := by
      intro v hv htrue hcon
      exact (mem_newVFam.mp hv).2.2 (mem_isoCov.mpr ⟨_, hcon, (hwit v hv).2⟩)
    have hblk_meet : ∀ v ∈ newVFam 𝓖 ω ω' S, ω (witIso 𝓖 ω' e₀ v) = true →
        ((blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v) : Set V) ∩ (witIso 𝓖 ω' e₀ v : Set V)).Nonempty := by
      intro v hv htrue
      exact (blockerOf_spec 𝓖 ω _ (exists_blocker 𝓖 htrue (hblk_notiso v hv htrue))).2.2
    have hblk_false : ∀ v ∈ newVFam 𝓖 ω ω' S, ω (witIso 𝓖 ω' e₀ v) = true →
        ω' (blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v)) = false := by
      intro v hv htrue
      exact blockerOf_eq_false_of_mem_iso 𝓖 (hwit v hv).1
        (exists_blocker 𝓖 htrue (hblk_notiso v hv htrue))
    have hblk_cert : ∀ v ∈ newVFam 𝓖 ω ω' S, ω (witIso 𝓖 ω' e₀ v) = true →
        blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v) ∈ certM 𝓖 ω S := by
      intro v hv htrue
      rw [mem_certM]
      refine Or.inr (Finset.mem_image.mpr ⟨witIso 𝓖 ω' e₀ v, ?_, rfl⟩)
      exact Finset.mem_filter.mpr ⟨hwit_thru v hv, htrue⟩
    have hfibB : ∀ i ∈ disOffV 𝓖 ω ω' S,
        ((newBV 𝓖 ω ω' e₀ S).filter
          (fun v => blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v) = i)).card ≤ r * r := by
      intro i hi
      set Fib : Finset V := (newBV 𝓖 ω ω' e₀ S).filter
        (fun v => blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v) = i) with hFib
      have hmemFib : ∀ v ∈ Fib, v ∈ newBV 𝓖 ω ω' e₀ S ∧
          blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v) = i := by
        intro v hv
        rw [hFib, Finset.mem_filter] at hv
        exact hv
      have hWi : (Fib.image (witIso 𝓖 ω' e₀)).card ≤ r := by
        refine card_le_eFin_card_of_pairwiseDisjoint_meets (i := i) huni ?_ ?_
        · intro e he f hf hef
          obtain ⟨ve, hve, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨vf, hvf, rfl⟩ := Finset.mem_image.mp hf
          exact (isofam_matching 𝓖 ω' huni).1 _ _
            (hwit ve (mem_newBV.mp (hmemFib ve hve).1).1).1
            (hwit vf (mem_newBV.mp (hmemFib vf hvf).1).1).1 hef
        · intro e he
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
          have hbv := hmemFib v hv
          have h1 := hblk_meet v (mem_newBV.mp hbv.1).1 (mem_newBV.mp hbv.1).2
          rw [hbv.2] at h1
          simpa [Set.inter_comm] using h1
      have hmapsW : Set.MapsTo (witIso 𝓖 ω' e₀) ↑Fib ↑(Fib.image (witIso 𝓖 ω' e₀)) :=
        fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hfibW : ∀ e ∈ Fib.image (witIso 𝓖 ω' e₀),
          (Fib.filter (fun v => witIso 𝓖 ω' e₀ v = e)).card ≤ r := by
        intro e he
        have hle : Fib.filter (fun v => witIso 𝓖 ω' e₀ v = e) ⊆ eFin 𝓖 e := by
          intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨hvF, hw⟩ := hv
          have hvV : v ∈ newVFam 𝓖 ω ω' S := (mem_newBV.mp (hmemFib v hvF).1).1
          have hmem : v ∈ (witIso 𝓖 ω' e₀ v : Set V) := (hwit v hvV).2
          rw [hw] at hmem
          exact (eFin_mem_iff 𝓖).mpr hmem
        calc (Fib.filter (fun v => witIso 𝓖 ω' e₀ v = e)).card ≤ (eFin 𝓖 e).card :=
              Finset.card_le_card hle
          _ = r := eFin_card_of_hunif huni e
      calc Fib.card = ∑ e ∈ Fib.image (witIso 𝓖 ω' e₀),
              (Fib.filter (fun v => witIso 𝓖 ω' e₀ v = e)).card :=
            Finset.card_eq_sum_card_fiberwise hmapsW
        _ ≤ ∑ e ∈ Fib.image (witIso 𝓖 ω' e₀), r := Finset.sum_le_sum hfibW
        _ = (Fib.image (witIso 𝓖 ω' e₀)).card * r := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ r * r := Nat.mul_le_mul_right r hWi
    have hstep3b : (newBV 𝓖 ω ω' e₀ S).card ≤ (disOffV 𝓖 ω ω' S).card * (r * r) := by
      have hmaps : Set.MapsTo (fun v => blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v))
          ↑(newBV 𝓖 ω ω' e₀ S) ↑(disOffV 𝓖 ω ω' S) := by
        intro v hv
        obtain ⟨hvV, htrue⟩ := mem_newBV.mp hv
        have hspec := blockerOf_spec 𝓖 ω _ (exists_blocker 𝓖 htrue (hblk_notiso v hvV htrue))
        refine Finset.mem_filter.mpr ⟨?_, hspec.2.1⟩
        refine Finset.mem_filter.mpr ⟨hblk_cert v hvV htrue, ?_⟩
        rw [hspec.2.1, hblk_false v hvV htrue]
        simp
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      calc ∑ i ∈ disOffV 𝓖 ω ω' S,
            ((newBV 𝓖 ω ω' e₀ S).filter
              (fun v => blockerOf 𝓖 ω (witIso 𝓖 ω' e₀ v) = i)).card
          ≤ ∑ i ∈ disOffV 𝓖 ω ω' S, r * r := Finset.sum_le_sum hfibB
        _ = (disOffV 𝓖 ω ω' S).card * (r * r) := by rw [Finset.sum_const, smul_eq_mul]
    have hJsplit : (disOnV 𝓖 ω ω' S).card + (disOffV 𝓖 ω ω' S).card
        ≤ (disJV 𝓖 ω ω' S).card := by
      have hsub : disOnV 𝓖 ω ω' S ∪ disOffV 𝓖 ω ω' S ⊆ disJV 𝓖 ω ω' S := by
        intro e he
        rcases Finset.mem_union.mp he with h | h
        · exact (mem_disOnV.mp h).1
        · exact (mem_disOffV.mp h).1
      have hdisj : Disjoint (disOnV 𝓖 ω ω' S) (disOffV 𝓖 ω ω' S) := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        have h1 : ω e = false := (mem_disOnV.mp he1).2
        have h2 : ω e = true := (mem_disOffV.mp he2).2
        rw [h1] at h2
        exact Bool.noConfusion h2
      calc (disOnV 𝓖 ω ω' S).card + (disOffV 𝓖 ω ω' S).card
          = (disOnV 𝓖 ω ω' S ∪ disOffV 𝓖 ω ω' S).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (disJV 𝓖 ω ω' S).card := Finset.card_le_card hsub
    have hVbound : (newVFam 𝓖 ω ω' S).card ≤ r * r * (disJV 𝓖 ω ω' S).card := by
      have hrr : r ≤ r * r := Nat.le_mul_of_pos_left r (by omega)
      have hJon : (disOnV 𝓖 ω ω' S).card ≤ (disJV 𝓖 ω ω' S).card :=
        le_trans (Nat.le_add_right _ _) hJsplit
      have hJoff : (disOffV 𝓖 ω ω' S).card ≤ (disJV 𝓖 ω ω' S).card :=
        le_trans (Nat.le_add_left _ _) hJsplit
      calc (newVFam 𝓖 ω ω' S).card
          ≤ (newAV 𝓖 ω ω' e₀ S).card + (newBV 𝓖 ω ω' e₀ S).card := hstep2
        _ ≤ (disOnV 𝓖 ω ω' S).card * r + (disOffV 𝓖 ω ω' S).card * (r * r) :=
            Nat.add_le_add hstep3a hstep3b
        _ ≤ r * r * (disOnV 𝓖 ω ω' S).card + r * r * (disOffV 𝓖 ω ω' S).card := by
            refine Nat.add_le_add ?_ ?_
            · calc (disOnV 𝓖 ω ω' S).card * r ≤ (disOnV 𝓖 ω ω' S).card * (r * r) :=
                  Nat.mul_le_mul_left _ hrr
                _ = r * r * (disOnV 𝓖 ω ω' S).card := Nat.mul_comm _ _
            · rw [Nat.mul_comm ((disOffV 𝓖 ω ω' S).card) (r * r)]
        _ = r * r * ((disOnV 𝓖 ω ω' S).card + (disOffV 𝓖 ω ω' S).card) := by ring
        _ ≤ r * r * (disJV 𝓖 ω ω' S).card := Nat.mul_le_mul_left _ hJsplit
    have hcast : ((newVFam 𝓖 ω ω' S).card : ℝ) < u := by
      have h1 : ((newVFam 𝓖 ω ω' S).card : ℝ)
          ≤ ((r * r * (disJV 𝓖 ω ω' S).card : ℕ) : ℝ) := by exact_mod_cast hVbound
      have h2 : ((r * r * (disJV 𝓖 ω ω' S).card : ℕ) : ℝ)
          = (r:ℝ) ^ 2 * ((disJV 𝓖 ω ω' S).card : ℝ) := by push_cast; ring
      have h3 : (r:ℝ) ^ 2 * ((disJV 𝓖 ω ω' S).card : ℝ) < (r:ℝ)^2 * (u / (r:ℝ)^2) :=
        mul_lt_mul_of_pos_left hcard (by positivity)
      have h4 : (r:ℝ)^2 * (u / (r:ℝ)^2) = u := by
        have hne : (r:ℝ)^2 ≠ 0 := by positivity
        exact mul_div_cancel₀ u hne
      linarith
    have hfin : ((matchedFam 𝓖 ω' S : ℕ) : ℝ)
        ≤ ((matchedFam 𝓖 ω S : ℕ) : ℝ) + ((newVFam 𝓖 ω ω' S).card : ℝ) := by
      have h1 : ((matchedFam 𝓖 ω' S : ℕ) : ℝ)
          ≤ ((matchedFam 𝓖 ω S + (newVFam 𝓖 ω ω' S).card : ℕ) : ℝ) := by
        exact_mod_cast hstep1
      have h2 : ((matchedFam 𝓖 ω S + (newVFam 𝓖 ω ω' S).card : ℕ) : ℝ)
          = ((matchedFam 𝓖 ω S : ℕ) : ℝ) + ((newVFam 𝓖 ω ω' S).card : ℝ) := by push_cast; ring
      linarith
    linarith


/-! ## Degenerate measures

For `p = 0` and `p = 1` the product measure is concentrated on a single outcome,
so the deviation event is empty. -/

lemma prob_abs_sub_exp_le_of_support_eq {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (X : Ω → ℝ)
    (ω₀ : Ω) {t C : ℝ} (hwt : ∀ ω, ω ≠ ω₀ → μ.wt ω = 0) (hwt0 : μ.wt ω₀ = 1)
    (ht : 0 < t) (hC : 0 ≤ C) :
    μ.prob {ω | t ≤ |X ω - μ.exp X|} ≤ C := by
  classical
  have hexp : μ.exp X = X ω₀ := by
    rw [FinProb.exp, Finset.sum_eq_single ω₀]
    · rw [hwt0, one_mul]
    · intro ω _ hω
      rw [hwt ω hω, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ ω₀) h
  have hzero : μ.prob {ω | t ≤ |X ω - μ.exp X|} = 0 := by
    rw [FinProb.prob]
    refine Finset.sum_eq_zero fun ω _ => ?_
    by_cases h : ω ∈ {ω' | t ≤ |X ω' - μ.exp X|}
    · rw [if_pos h]
      have hP : t ≤ |X ω - μ.exp X| := h
      by_cases hω : ω = ω₀
      · exfalso
        rw [hω, hexp] at hP
        simp only [sub_self, abs_zero] at hP
        linarith
      · exact hwt ω hω
    · rw [if_neg h]
  rw [hzero]
  exact hC

lemma prob_le_of_eq_const_zero {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (X : Ω → ℝ)
    (hX : X = fun _ => 0) {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) :
    μ.prob {ω | t ≤ |X ω - μ.exp X|} ≤ C := by
  classical
  have hexp : μ.exp X = 0 := by rw [hX, FinProb.exp_const]
  have hempty : {ω | t ≤ |X ω - μ.exp X|} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [hexp, hX]
    simp only [Pi.zero_apply, sub_zero, abs_zero]
    exact not_le.mpr ht
  rw [hempty, FinProb.prob_empty]
  exact hC

lemma edgeMeasure_wt_eq_zero_of_p_eq_zero {𝓖 : Set (Set V)} {p : ℝ} {h0 : 0 ≤ p} {h1 : p ≤ 1}
    (hp : p = 0) {ω : 𝓖 → Bool} (hω : ω ≠ fun _ => false) :
    (edgeMeasure 𝓖 p h0 h1).wt ω = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : 𝓖, ω e = true := by
    by_contra hc
    push_neg at hc
    exact hω (funext fun e => by
      rcases Bool.eq_false_or_eq_true (ω e) with h | h
      · exact absurd h (hc e)
      · exact h)
  rw [edgeMeasure, FinProb.pi_wt]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he, hp])

lemma edgeMeasure_wt_eq_one_of_p_eq_zero {𝓖 : Set (Set V)} {p : ℝ} {h0 : 0 ≤ p} {h1 : p ≤ 1}
    (hp : p = 0) : (edgeMeasure 𝓖 p h0 h1).wt (fun _ => false) = 1 := by
  rw [edgeMeasure, FinProb.pi_wt]
  simp [hp]

lemma edgeMeasure_wt_eq_zero_of_p_eq_one {𝓖 : Set (Set V)} {p : ℝ} {h0 : 0 ≤ p} {h1 : p ≤ 1}
    (hp : p = 1) {ω : 𝓖 → Bool} (hω : ω ≠ fun _ => true) :
    (edgeMeasure 𝓖 p h0 h1).wt ω = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : 𝓖, ω e = false := by
    by_contra hc
    push_neg at hc
    exact hω (funext fun e => by
      rcases Bool.eq_false_or_eq_true (ω e) with h | h
      · exact h
      · exact absurd h (hc e))
  rw [edgeMeasure, FinProb.pi_wt]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he, hp])

lemma edgeMeasure_wt_eq_one_of_p_eq_one {𝓖 : Set (Set V)} {p : ℝ} {h0 : 0 ≤ p} {h1 : p ≤ 1}
    (hp : p = 1) : (edgeMeasure 𝓖 p h0 h1).wt (fun _ => true) = 1 := by
  rw [edgeMeasure, FinProb.pi_wt]
  simp [hp]

/-! ## The matched-coverage tail bound -/

theorem r2_Mfam_tail {V : Type*} [Fintype V] [DecidableEq V] {𝓖 : Set (Set V)} {r : ℕ}
    (hr : 2 ≤ r) (huni : Work.Deep.Nibble.HUnif 𝓖 r) {θ : ℝ} (hθ0 : 0 < θ) {D : ℕ}
    (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hdeg : ∀ v : V, ((Work.Deep.Nibble.hd 𝓖 v : ℝ)) ≤ 2 * (D : ℝ))
    (S : Finset V) {t : ℝ}
    (ht : 50 * (r : ℝ) ^ 2 * Real.sqrt (4 * (r : ℝ) * (D : ℝ) * (S.card : ℝ)) < t) :
    (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t ≤ |((Work.Deep.Nibble.matchedFam 𝓖 ω S : ℕ) : ℝ)
          - (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
              (fun ω => ((Work.Deep.Nibble.matchedFam 𝓖 ω S : ℕ) : ℝ))|}
      ≤ 4 * Real.exp (- t ^ 2 / (64 * (r : ℝ) ^ 5 * (D : ℝ) * (S.card : ℝ))) := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrR1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have htpos : 0 < t := by
    have h1 : (0:ℝ) ≤ Real.sqrt (4 * (r:ℝ) * (D:ℝ) * (S.card:ℝ)) := Real.sqrt_nonneg _
    nlinarith [ht, sq_nonneg (r:ℝ), h1]
  have htarget : (0:ℝ) < 4 * Real.exp (- t ^ 2 / (64 * (r:ℝ)^5 * (D:ℝ) * (S.card:ℝ))) := by
    positivity
  rcases eq_or_lt_of_le hp0 with hp0eq | hp0gt
  · have hp0z : θ / (D:ℝ) = 0 := hp0eq.symm
    have h := prob_abs_sub_exp_le_of_support_eq (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1)
      (fun ω : 𝓖 → Bool => ((matchedFam 𝓖 ω S : ℕ) : ℝ)) (fun _ => false)
      (fun ω hω => edgeMeasure_wt_eq_zero_of_p_eq_zero hp0z hω)
      (edgeMeasure_wt_eq_one_of_p_eq_zero hp0z) htpos htarget.le
    exact h
  · rcases lt_or_eq_of_le hp1 with hp1lt | hp1eq
    · rcases Nat.eq_zero_or_pos S.card with hS0 | hSpos
      · have hX : (fun ω : 𝓖 → Bool => ((matchedFam 𝓖 ω S : ℕ) : ℝ)) = fun _ => 0 := by
          funext ω
          have hz : matchedFam 𝓖 ω S = 0 := by
            rw [matchedFam_eq_isoCov_card 𝓖 ω S, Finset.card_eq_zero.mp hS0]
            simp
          rw [hz]
          simp
        exact prob_le_of_eq_const_zero (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) _ hX htpos htarget.le
      · by_cases hG : 𝓖.Nonempty
        · obtain ⟨e₀, he₀⟩ := hG
          let e₁ : 𝓖 := ⟨e₀, he₀⟩
          have hVne : Nonempty V := by
            obtain ⟨v, -⟩ := Finset.card_pos.mp hSpos
            exact ⟨v⟩
          have hM1 : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
            have h : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hVne
            exact_mod_cast h
          have hs1 : 1 ≤ 4 * D * S.card := by nlinarith [hD, hSpos]
          have hfull : ∀ (i : 𝓖) (x : Bool), 0 < (boolProb (θ/(D:ℝ)) hp0 hp1).wt x := by
            intro i x
            cases x with
            | true => simpa using hp0gt
            | false =>
                simp only [boolProb_wt_false]
                linarith
          have hsup : ∀ ω : 𝓖 → Bool, |((matchedFam 𝓖 ω S : ℕ) : ℝ)| ≤ (Fintype.card V : ℝ) := by
            intro ω
            rw [abs_of_nonneg (Nat.cast_nonneg _)]
            calc ((matchedFam 𝓖 ω S : ℕ) : ℝ) ≤ (S.card : ℝ) := by
                  exact_mod_cast matchedFam_le_card 𝓖 ω S
              _ ≤ (Fintype.card V : ℝ) := by exact_mod_cast Finset.card_le_univ S
          have hcert : ∀ u : ℝ, 0 < u → ∀ ω : 𝓖 → Bool, ω ∉ (∅ : Set (𝓖 → Bool)) →
              ∃ I : Finset 𝓖, I.card ≤ 4 * D * S.card ∧
                ∀ ω' : 𝓖 → Bool, ω' ∉ (∅ : Set (𝓖 → Bool)) →
                  ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r:ℝ)^2 →
                    ((matchedFam 𝓖 ω' S : ℕ) : ℝ) < ((matchedFam 𝓖 ω S : ℕ) : ℝ) + u := by
            intro u hu ω _
            refine ⟨certM 𝓖 ω S, certM_card_le 𝓖 ω S hdeg, fun ω' _ hlt => ?_⟩
            exact matchedFam_lt_add_of_card_lt hr1 huni e₁ S ω ω' hlt
          have hc1 : (1:ℝ) ≤ (r:ℝ)^2 := by nlinarith [hrR1]
          have hexc : (FinProb.pi (fun _ : 𝓖 => boolProb (θ/(D:ℝ)) hp0 hp1)).prob
              (∅ : Set (𝓖 → Bool)) ≤ 1 / (Fintype.card V : ℝ)^2 := by
            rw [FinProb.prob_empty]
            positivity
          have h4D : ((4 * D * S.card : ℕ) : ℝ) = 4 * (D:ℝ) * (S.card:ℝ) := by push_cast; ring
          have htt : 50 * (r:ℝ)^2 * Real.sqrt ((4 * D * S.card : ℕ) : ℝ) < t := by
            have h3 : 4 * (D:ℝ) * (S.card:ℝ) ≤ 4 * (r:ℝ) * (D:ℝ) * (S.card:ℝ) := by
              have hDnn : (0:ℝ) ≤ (D:ℝ) := le_of_lt hDpos
              have hSnn : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
              nlinarith [hrR1, hDnn, hSnn]
            have h5 : Real.sqrt ((4 * D * S.card : ℕ) : ℝ) ≤
                Real.sqrt (4 * (r:ℝ) * (D:ℝ) * (S.card:ℝ)) := by
              rw [h4D]
              exact Real.sqrt_le_sqrt h3
            have h6 : 50 * (r:ℝ)^2 * Real.sqrt ((4 * D * S.card : ℕ) : ℝ)
                ≤ 50 * (r:ℝ)^2 * Real.sqrt (4 * (r:ℝ) * (D:ℝ) * (S.card:ℝ)) :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
            linarith
          have hgoal := bj_talagrand (μ := fun _ : 𝓖 => boolProb (θ/(D:ℝ)) hp0 hp1) hfull
            (fun ω : 𝓖 → Bool => ((matchedFam 𝓖 ω S : ℕ) : ℝ)) (Fintype.card V : ℝ) hM1 hsup
            ((r:ℝ)^2) hc1 (4 * D * S.card) hs1
            (∅ : Set (𝓖 → Bool)) hexc hcert t htt
          rw [FinProb.prob_empty, mul_zero, add_zero] at hgoal
          refine le_trans hgoal ?_
          have h5r : (r:ℝ) ≤ (r:ℝ)^5 := by
            have h4 : (1:ℝ) ≤ (r:ℝ)^4 := one_le_pow₀ hrR1
            calc (r:ℝ) = (r:ℝ) * 1 := by ring
              _ ≤ (r:ℝ) * (r:ℝ)^4 := mul_le_mul_of_nonneg_left h4 hrR.le
              _ = (r:ℝ)^5 := by ring
          have hden : 16 * ((r:ℝ)^2)^2 * ((4 * D * S.card : ℕ) : ℝ)
              ≤ 64 * (r:ℝ)^5 * (D:ℝ) * (S.card:ℝ) := by
            rw [h4D]
            have h45 : (r:ℝ)^4 ≤ (r:ℝ)^5 := by
              calc (r:ℝ)^4 = (r:ℝ)^4 * 1 := by ring
                _ ≤ (r:ℝ)^4 * (r:ℝ) := mul_le_mul_of_nonneg_left hrR1 (pow_nonneg hrR.le 4)
                _ = (r:ℝ)^5 := by ring
            have hnn : (0:ℝ) ≤ 64 * (D:ℝ) * (S.card:ℝ) := by positivity
            calc 16 * ((r:ℝ)^2)^2 * (4 * (D:ℝ) * (S.card:ℝ))
                = (r:ℝ)^4 * (64 * (D:ℝ) * (S.card:ℝ)) := by ring
              _ ≤ (r:ℝ)^5 * (64 * (D:ℝ) * (S.card:ℝ)) := mul_le_mul_of_nonneg_right h45 hnn
              _ = 64 * (r:ℝ)^5 * (D:ℝ) * (S.card:ℝ) := by ring
          have hApos : (0:ℝ) < 16 * ((r:ℝ)^2)^2 * ((4 * D * S.card : ℕ) : ℝ) := by
            rw [h4D]
            have hSpos' : (0:ℝ) < (S.card:ℝ) := by exact_mod_cast hSpos
            positivity
          have hexp_le : Real.exp (- t^2 / (16 * ((r:ℝ)^2)^2 * ((4 * D * S.card : ℕ) : ℝ)))
              ≤ Real.exp (- t^2 / (64 * (r:ℝ)^5 * (D:ℝ) * (S.card:ℝ))) := by
            refine Real.exp_le_exp.mpr ?_
            have hdiv := div_le_div_of_nonneg_left (sq_nonneg t) hApos hden
            rw [neg_div, neg_div]
            exact neg_le_neg hdiv
          exact mul_le_mul_of_nonneg_left hexp_le (by norm_num)
        · have hG' : 𝓖 = ∅ := Set.not_nonempty_iff_eq_empty.mp hG
          have hemptyG : ∀ x : Set V, x ∉ (𝓖 : Set (Set V)) := by
            intro x
            rw [hG']
            simp
          have hiso : ∀ ω : 𝓖 → Bool, isoFam 𝓖 ω = ∅ := by
            intro ω
            ext e
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun _ => hemptyG e.1 e.2
          have hz : ∀ ω : 𝓖 → Bool, matchedFam 𝓖 ω S = 0 := by
            intro ω
            rw [matchedFam_eq_isoCov_card 𝓖 ω S]
            have hcov : isoCov 𝓖 ω = ∅ := by rw [isoCov, hiso ω]; simp
            rw [hcov]
            simp
          have hX : (fun ω : 𝓖 → Bool => ((matchedFam 𝓖 ω S : ℕ) : ℝ)) = fun _ => 0 := by
            funext ω
            rw [hz ω]
            simp
          exact prob_le_of_eq_const_zero (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) _ hX htpos htarget.le
    · have h := prob_abs_sub_exp_le_of_support_eq (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1)
        (fun ω : 𝓖 → Bool => ((matchedFam 𝓖 ω S : ℕ) : ℝ)) (fun _ => true)
        (fun ω hω => edgeMeasure_wt_eq_zero_of_p_eq_one hp1eq hω)
        (edgeMeasure_wt_eq_one_of_p_eq_one hp1eq) htpos htarget.le
      exact h

end Work.Deep.Nibble
