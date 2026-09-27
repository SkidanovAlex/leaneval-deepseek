import Mathlib

/-!
# Hyperplane slices of a compact curve are totally disconnected

Let `K ⊆ ℝ` be compact and `h : ℝ → ℝⁿ` be continuous and injective on `K`.  Then there is a
nonzero direction `u` such that for every level `s` the slice of the curve `h '' K` by the
hyperplane `{z | ⟪z - a, u⟫ = s}` is totally disconnected.

The set of *bad* directions — those `u` for which `⟪h ·, u⟫` is constant on some nondegenerate
subinterval of `K` — is the union of the sets `levelBad h a b` over all rational intervals
`[a,b] ⊆ K`.  Each `levelBad h a b` is a proper closed linear subspace of `ℝⁿ` (proper because
`⟪h b - h a, u⟫` vanishes at `t = b`, while `h b ≠ h a` by injectivity, and there are only
countably many rational intervals, so Baire's theorem provides a direction outside all of them.
For such a direction every level set of `⟪h ·, u⟫` is a closed subset of `ℝ` containing no
nondegenerate interval, hence totally disconnected, and it is carried homeomorphically onto its
image by `h` (which is an embedding on the compact set `K`).
-/

open Set Metric Topology Filter
open scoped Topology

namespace Work.Whitney.PathTools
namespace Slices

variable {n : ℕ}

/-- The submodule of directions `u` for which the `u`-projection of `h` is constant on `[a,b]`,
i.e. `⟪h t - h a, u⟫ = 0` for every `t ∈ [a,b]`. -/
noncomputable def levelBad (h : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  ⨅ (t : ↥(Set.Icc a b)), LinearMap.ker ((innerSL ℝ (h t - h a)).toLinearMap)

lemma mem_levelBad (h : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ)
    (u : EuclideanSpace ℝ (Fin n)) :
    u ∈ levelBad h a b ↔ ∀ t ∈ Set.Icc a b, inner ℝ (h t - h a) u = 0 := by
  rw [levelBad]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hh t ht
    simpa [inner_sub_left] using hh ⟨t, ht⟩
  · intro hh t
    simpa [inner_sub_left] using hh t.1 t.2

lemma isClosed_levelBad (h : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    IsClosed (levelBad h a b : Set (EuclideanSpace ℝ (Fin n))) := by
  have hcoe : (levelBad h a b : Set (EuclideanSpace ℝ (Fin n)))
      = {u | ∀ t ∈ Set.Icc a b, inner ℝ (h t - h a) u = 0} := by
    ext u; exact mem_levelBad h a b u
  rw [hcoe]
  have hset : {u : EuclideanSpace ℝ (Fin n) | ∀ t ∈ Set.Icc a b, inner ℝ (h t - h a) u = 0}
      = ⋂ t ∈ Set.Icc a b, {u : EuclideanSpace ℝ (Fin n) | inner ℝ (h t - h a) u = 0} := by
    ext u; simp
  rw [hset]
  exact isClosed_biInter fun t _ =>
    isClosed_eq (continuous_const.inner continuous_id) continuous_const

/-- `levelBad h a b` is a proper subspace, provided `a < b` are two points of `K` and `h` is
injective on `K`. -/
lemma levelBad_ne_top {K : Set ℝ} {h : ℝ → EuclideanSpace ℝ (Fin n)} (hinj : Set.InjOn h K)
    {a b : ℝ} (ha : a ∈ K) (hb : b ∈ K) (hab : a < b) : levelBad h a b ≠ ⊤ := by
  intro htop
  have hmem : h b - h a ∈ levelBad h a b := by rw [htop]; trivial
  have hzero : h b - h a = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp
      ((mem_levelBad h a b (h b - h a)).mp hmem b ⟨le_of_lt hab, le_rfl⟩)
  exact absurd (hinj ha hb (sub_eq_zero.mp hzero).symm) (ne_of_lt hab)

lemma not_nonempty_interior_levelBad {K : Set ℝ} {h : ℝ → EuclideanSpace ℝ (Fin n)}
    (hinj : Set.InjOn h K) {a b : ℝ} (ha : a ∈ K) (hb : b ∈ K) (hab : a < b) :
    ¬ (interior (levelBad h a b : Set (EuclideanSpace ℝ (Fin n)))).Nonempty :=
  fun hne => levelBad_ne_top hinj ha hb hab (Submodule.eq_top_of_nonempty_interior' _ hne)

/-- `ℝⁿ` is nontrivial as soon as `n ≥ 1`. -/
lemma nontrivial_euclidean (hn : 1 ≤ n) : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)

/-- Index of the family of bad direction sets: the origin, or a rational interval contained in
`K`. -/
abbrev BadIdx (K : Set ℝ) : Type _ :=
  Option {p : ℚ × ℚ // p.1 < p.2 ∧ Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ K}

/-- The family of bad direction sets. -/
noncomputable def badFamily (K : Set ℝ) (h : ℝ → EuclideanSpace ℝ (Fin n)) :
    BadIdx K → Set (EuclideanSpace ℝ (Fin n))
  | none => {0}
  | some p => (levelBad h (p.val.1 : ℝ) (p.val.2 : ℝ) : Set (EuclideanSpace ℝ (Fin n)))

/-- There is a nonzero direction `u` such that `⟪h ·, u⟫` is not constant on any nondegenerate
interval with rational endpoints inside `K`. -/
theorem exists_good_dir {K : Set ℝ} {h : ℝ → EuclideanSpace ℝ (Fin n)} (hn : 1 ≤ n)
    (hinj : Set.InjOn h K) :
    ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧
      ∀ p : ℚ × ℚ, p.1 < p.2 → Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ K →
        ∃ t ∈ Set.Icc (p.1 : ℝ) (p.2 : ℝ), inner ℝ (h t - h (p.1 : ℝ)) u ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hcover : (⋃ p : BadIdx K, badFamily K h p) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    by_cases hu : u = 0
    · exact Set.mem_iUnion.mpr ⟨none, by simp [badFamily, hu]⟩
    · obtain ⟨p, hp1, hp2, hzero⟩ := hcon u hu
      exact Set.mem_iUnion.mpr ⟨some ⟨p, hp1, hp2⟩, by
        simp only [badFamily]
        exact (mem_levelBad h (p.1 : ℝ) (p.2 : ℝ) u).mpr hzero⟩
  have hclosed : ∀ p : BadIdx K, IsClosed (badFamily K h p) := by
    intro p
    cases p with
    | none => simp only [badFamily]; exact isClosed_singleton
    | some q => simp only [badFamily]; exact isClosed_levelBad h (q.val.1 : ℝ) (q.val.2 : ℝ)
  have hnot : ∀ p : BadIdx K, ¬ (interior (badFamily K h p)).Nonempty := by
    intro p
    cases p with
    | none =>
      simp only [badFamily]
      haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := nontrivial_euclidean hn
      intro h
      have htop : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) = ⊤ :=
        Submodule.eq_top_of_nonempty_interior' _ (by simpa using h)
      have hsub : Subsingleton (EuclideanSpace ℝ (Fin n)) := ⟨fun a b => by
        have ha : a ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := htop ▸ Submodule.mem_top
        have hb : b ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := htop ▸ Submodule.mem_top
        rw [Submodule.mem_bot] at ha hb
        rw [ha, hb]⟩
      exact not_subsingleton_iff_nontrivial.mpr ‹Nontrivial _› hsub
    | some q =>
      simp only [badFamily]
      have hq : (q.val.1 : ℝ) < (q.val.2 : ℝ) := by exact_mod_cast q.property.1
      have hq1K : (q.val.1 : ℝ) ∈ K :=
        q.property.2 (show (q.val.1 : ℝ) ∈ Set.Icc (q.val.1 : ℝ) (q.val.2 : ℝ) from
          ⟨le_rfl, le_of_lt hq⟩)
      have hq2K : (q.val.2 : ℝ) ∈ K :=
        q.property.2 (show (q.val.2 : ℝ) ∈ Set.Icc (q.val.1 : ℝ) (q.val.2 : ℝ) from
          ⟨le_of_lt hq, le_rfl⟩)
      exact not_nonempty_interior_levelBad hinj hq1K hq2K hq
  obtain ⟨p, hp⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  exact hnot p hp

end Slices

open Slices

theorem slices_totallyDisconnected {n : ℕ} (hn : 1 ≤ n)
    {K : Set ℝ} (hK : IsCompact K) {h : ℝ → EuclideanSpace ℝ (Fin n)}
    (hh : ContinuousOn h K) (hinj : Set.InjOn h K) (a : EuclideanSpace ℝ (Fin n)) :
    ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧
      ∀ s : ℝ, IsTotallyDisconnected
        (h '' K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - a) u = s}) := by
  obtain ⟨u, hu0, hu⟩ := exists_good_dir (n := n) hn hinj
  refine ⟨u, hu0, fun s => ?_⟩
  -- the parameter set of the slice
  set c : ℝ := s + inner ℝ a u with hc
  set S : Set ℝ := {t : ℝ | t ∈ K ∧ inner ℝ (h t) u = c} with hS
  -- ## Step 1: `S` is totally disconnected
  have hStd : IsTotallyDisconnected S := by
    rw [isTotallyDisconnected_iff_lt]
    intro x hx y hy hxy
    by_contra hcon
    have hsub : Set.Ioo x y ⊆ S := by
      intro z hz
      by_contra hzS
      exact hcon ⟨z, hzS, hz⟩
    obtain ⟨q₁, hxq₁, hq₁y⟩ := exists_rat_btwn hxy
    obtain ⟨q₂, hq₁q₂, hq₂y⟩ := exists_rat_btwn hq₁y
    have hlt : (q₁ : ℚ) < q₂ := by exact_mod_cast hq₁q₂
    have hIccK : Set.Icc (q₁ : ℝ) (q₂ : ℝ) ⊆ K := by
      intro t ht
      have htxy : t ∈ Set.Ioo x y := ⟨lt_of_lt_of_le hxq₁ ht.1, lt_of_le_of_lt ht.2 hq₂y⟩
      exact (hsub htxy).1
    obtain ⟨t, ht, hne⟩ := hu (q₁, q₂) hlt hIccK
    have htS : t ∈ S := hsub ⟨lt_of_lt_of_le hxq₁ ht.1, lt_of_le_of_lt ht.2 hq₂y⟩
    have hq₁S : (q₁ : ℝ) ∈ S := hsub ⟨hxq₁, lt_trans hq₁q₂ hq₂y⟩
    rw [inner_sub_left] at hne
    rw [htS.2, hq₁S.2] at hne
    exact hne (sub_self c)
  -- ## Step 2: describe the slice as `h '' S`
  have hset : h '' K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - a) u = s} = h '' S := by
    ext z
    constructor
    · rintro ⟨hz, hzin⟩
      obtain ⟨t, htK, rfl⟩ := hz
      refine ⟨t, ⟨htK, ?_⟩, rfl⟩
      change inner ℝ (h t - a) u = s at hzin
      rw [inner_sub_left] at hzin
      show inner ℝ (h t) u = c
      rw [hc]; linarith
    · rintro ⟨t, htS, rfl⟩
      refine ⟨⟨t, htS.1, rfl⟩, ?_⟩
      show inner ℝ (h t - a) u = s
      have h2 : inner ℝ (h t) u = s + inner ℝ a u := by rw [← hc]; exact htS.2
      rw [inner_sub_left]
      linarith
  rw [hset]
  -- ## Step 3: transfer total disconnectedness along `h`
  set Ssub : Set ↥K := Subtype.val ⁻¹' S with hSsub
  have hSsub_mem : ∀ t : ↥K, t ∈ Ssub ↔ (t : ℝ) ∈ S := by
    intro t
    rw [hSsub, Set.mem_preimage]
  have hSsub_eq : Subtype.val '' Ssub = S := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hSsub_mem s).mp hs
    · intro ht
      exact ⟨⟨t, ht.1⟩, (hSsub_mem ⟨t, ht.1⟩).mpr ht, rfl⟩
  have hStd' : IsTotallyDisconnected Ssub :=
    (Topology.IsEmbedding.subtypeVal.isTotallyDisconnected_image (s := Ssub)).mp (by
      rw [hSsub_eq]; exact hStd)
  haveI : TotallyDisconnectedSpace ↥Ssub := totallyDisconnectedSpace_subtype_iff.mpr hStd'
  have hSsub_closed : IsClosed Ssub := by
    have h1 : Ssub = {t : ↥K | inner ℝ (h (t : ℝ)) u = c} := by
      ext t
      rw [hSsub_mem t, hS]
      exact ⟨fun h => h.2, fun h => ⟨t.2, h⟩⟩
    rw [h1]
    exact isClosed_eq ((continuousOn_iff_continuous_domRestrict.mp hh).inner continuous_const)
      continuous_const
  haveI : CompactSpace ↥K := (isCompact_iff_compactSpace (s := K)).mp hK
  have hSsub_compact : IsCompact Ssub := hSsub_closed.isCompact
  haveI : CompactSpace ↥Ssub := isCompact_iff_compactSpace.mp hSsub_compact
  let f : ↥Ssub → EuclideanSpace ℝ (Fin n) := fun t => h ((t : ↥K) : ℝ)
  have hfcont : Continuous f :=
    (continuousOn_iff_continuous_domRestrict.mp hh).comp continuous_subtype_val
  have hfinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hval : ((t₁ : ↥K) : ℝ) = ((t₂ : ↥K) : ℝ) :=
      hinj (t₁ : ↥K).2 (t₂ : ↥K).2 h12
    exact Subtype.ext (Subtype.ext hval)
  have hfclosed : IsClosedMap f := fun s' hs' => (hs'.isCompact.image hfcont).isClosed
  have hemb : Topology.IsEmbedding f :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hfcont hfinj hfclosed).isEmbedding
  have hrange : f '' Set.univ = h '' S := by
    rw [Set.image_univ]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨((t : ↥K) : ℝ), (hSsub_mem (t : ↥K)).mp t.2, rfl⟩
    · rintro ⟨t, htS, rfl⟩
      exact ⟨⟨⟨t, htS.1⟩, (hSsub_mem ⟨t, htS.1⟩).mpr htS⟩, rfl⟩
  rw [← hrange]
  exact (hemb.isTotallyDisconnected_image (s := Set.univ)).mpr
    TotallyDisconnectedSpace.isTotallyDisconnected_univ

end Work.Whitney.PathTools
