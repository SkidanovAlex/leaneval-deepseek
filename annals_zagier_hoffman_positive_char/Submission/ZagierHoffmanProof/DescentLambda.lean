import Submission.ZagierHoffmanProof.DescentRelation

/-!
# The caller side of `descent_relation`: `ρ` built from the coefficients `lam`

WORK IN PROGRESS (NOT imported by `Submission.lean`; the build is unaffected).  Rebuilt in place,
top to bottom; see `Submission/PLAN.md` SESSION 324/325 for the design of what remains.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

theorem descent_lambda {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0)
    {w₀ : ℕ} {t₀ : ↥(tmI S)} (ht₀ : tmWeight t₀.1 = w₀)
    (hind : LinearIndependent (ambKperf F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} =>
        evalSeriesGen (tmL (Nat.card F) ω t.1.1) (ambTheta F)))
    {lam : ↥(tmI S) → Ambient F}
    (hlamem : ∀ t, tmWeight t.1 = w₀ → t ≠ t₀ → lam t ∈ ambKperf F)
    (hrel : evalSeriesGen (tmL (Nat.card F) ω t₀.1) (ambTheta F)
        = ∑ t ∈ (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ t₀)),
            lam t * evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) :
    ∀ t : ↥(tmI S), tmWeight t.1 = w₀ → t ≠ t₀ → lam t ∈ ambK F := by
  classical
  let Zl : List (ℕ × Polynomial (Ambient F)) → Ambient F :=
    fun u => evalSeriesGen (tmL (Nat.card F) ω u) (ambTheta F)
  let μ : List (ℕ × Polynomial (Ambient F)) → Ambient F :=
    fun u => if h : u ∈ tmI S then lam ⟨u, h⟩ else 0
  let ρ : Option ↥(tmI (descS S w₀)) → Ambient F := fun i => match i with
    | none => 0
    | some u => if u.1 = t₀.1 then 1 else if tmWeight u.1 = w₀ then -μ u.1 else 0
  have hμ : ∀ (u : ↥(tmI (descS S w₀))) (hu : tmWeight u.1 = w₀),
      μ u.1 = lam ⟨u.1, mem_tmI_of_mem_descW
        (mem_descW_of_mem_tmI_descS (S := S) (w₀ := w₀) hpos u.2 hu)⟩ := by
    intro u hu
    simp only [μ]
    rw [dif_pos (mem_tmI_of_mem_descW
      (mem_descW_of_mem_tmI_descS (S := S) (w₀ := w₀) hpos u.2 hu))]
  have hρtop : ρ (some (descT (F := F) (w₀ := w₀) t₀ ht₀)) = 1 := by
    simp only [ρ, descT_val, if_true]
  have hρ0 : ρ ≠ 0 := by
    intro h
    have h1 : (1 : Ambient F) = 0 := by
      have h2 := congrFun h (some (descT (F := F) (w₀ := w₀) t₀ ht₀))
      rw [hρtop] at h2
      simpa using h2
    exact one_ne_zero h1
  have hρmem : ∀ i, ρ i ∈ ambKperf F := by
    intro i
    cases i with
    | none => simp only [ρ]; exact Subfield.zero_mem _
    | some u =>
      simp only [ρ]
      by_cases h1 : u.1 = t₀.1
      · rw [if_pos h1]; exact Subfield.one_mem _
      · rw [if_neg h1]
        by_cases hw : tmWeight u.1 = w₀
        · rw [if_pos hw, hμ u hw]
          exact Subfield.neg_mem _ (hlamem _ hw (fun hh => h1 (Subtype.ext_iff.mp hh)))
        · rw [if_neg hw]; exact Subfield.zero_mem _
  -- ## the top-weight index set of the restricted motive, and the identity over `descW`
  set V : Finset (↥(tmI (descS S w₀))) :=
    Finset.univ.filter (fun u : ↥(tmI (descS S w₀)) => tmWeight u.1 = w₀) with hV
  have hVimg : V.image (fun u => u.1) = descW S w₀ := by
    rw [hV]
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_descW_of_mem_tmI_descS (S := S) (w₀ := w₀) hpos x.2 hx
    · intro hu
      refine ⟨⟨u, mem_tmI_descS_of_mem_descW hu⟩, ?_, rfl⟩
      show tmWeight u = w₀
      obtain ⟨t, ht, htu⟩ := mem_descW.mp hu
      rw [← htu]
      exact ht
  have hab : (∑ u ∈ V, μ u.1 * Zl u.1)
      = ∑ t ∈ (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀)),
          lam t * Zl t.1 := by
    have hL : (∑ u ∈ V, μ u.1 * Zl u.1) = ∑ z ∈ descW S w₀, μ z * Zl z := by
      have h := Finset.sum_image (f := fun z : List (ℕ × Polynomial (Ambient F)) => μ z * Zl z)
        (s := V) (g := fun u : ↥(tmI (descS S w₀)) => u.1) (fun x _ y _ h => Subtype.ext h)
      rw [hVimg] at h
      exact h.symm
    have hR : (∑ z ∈ descW S w₀, μ z * Zl z)
        = ∑ t ∈ (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀)),
            lam t * Zl t.1 := by
      rw [descW]
      rw [Finset.sum_image (f := fun z : List (ℕ × Polynomial (Ambient F)) => μ z * Zl z)
        (s := Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀))
        (g := fun t : ↥(tmI S) => t.1) (fun x _ y _ h => Subtype.ext h)]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hmem : t.1 ∈ tmI S := t.2
      have h2 : μ t.1 = lam t := by
        simp only [μ]
        rw [dif_pos hmem]
      rw [h2]
    exact hL.trans hR
  -- ## `hval`: the collapse and the termwise rewriting
  have hval : dotProduct ρ (fun i => evalSeriesGen (descPsi (F := F) w₀ ω ht₀ i) (ambTheta F))
      = 0 := by
    rw [dotProduct, Fintype.sum_option]
    have hnone : ρ none * evalSeriesGen (descPsi (F := F) w₀ ω ht₀ none) (ambTheta F) = 0 := by
      have h0 : ρ none = (0 : Ambient F) := rfl
      rw [h0, zero_mul]
    rw [hnone, zero_add]
    have hterm : ∀ u : ↥(tmI (descS S w₀)),
        ρ (some u) * evalSeriesGen (descPsi (F := F) w₀ ω ht₀ (some u)) (ambTheta F)
          = (if u.1 = t₀.1 then Zl u.1
             else if tmWeight u.1 = w₀ then -(μ u.1) * Zl u.1 else 0) := by
      intro u
      by_cases h1 : u.1 = t₀.1
      · have hρu : ρ (some u) = 1 := by
          simp only [ρ]
          rw [if_pos h1]
        have hψu : evalSeriesGen (descPsi (F := F) w₀ ω ht₀ (some u)) (ambTheta F) = Zl u.1 := by
          simp only [descPsi, tmPsiCol_some]
          rw [h1, ht₀, Nat.sub_self, pow_zero, mul_one]
        rw [hρu, hψu, if_pos h1, one_mul]
      · by_cases hw : tmWeight u.1 = w₀
        · have hρu : ρ (some u) = -(μ u.1) := by
            simp only [ρ]
            rw [if_neg h1, if_pos hw]
          have hψu : evalSeriesGen (descPsi (F := F) w₀ ω ht₀ (some u)) (ambTheta F) = Zl u.1 := by
            simp only [descPsi, tmPsiCol_some]
            rw [hw, Nat.sub_self, pow_zero, mul_one]
          rw [hρu, hψu, if_neg h1, if_pos hw]
        · have hρu : ρ (some u) = 0 := by
            simp only [ρ]
            rw [if_neg h1, if_neg hw]
          rw [hρu, zero_mul, if_neg h1, if_neg hw]
    rw [Finset.sum_congr rfl fun u _ => hterm u]
    -- (1) restrict the sum to `V`
    rw [← Finset.sum_subset
      (Finset.filter_subset (fun u : ↥(tmI (descS S w₀)) => tmWeight u.1 = w₀) Finset.univ) ?_]
    swap
    · intro u _ hu
      have hmem : u ∈ V ↔ tmWeight u.1 = w₀ := by
        rw [hV, Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
      by_cases h1 : u.1 = t₀.1
      · exact absurd (hmem.mpr (by rw [h1]; exact ht₀)) hu
      · rw [if_neg h1]
        by_cases hw : tmWeight u.1 = w₀
        · exact absurd (hmem.mpr hw) hu
        · rw [if_neg hw]
    -- (2) on `V` the inner `if` is true
    have hmemV : ∀ u : ↥(tmI (descS S w₀)), u ∈ V → tmWeight u.1 = w₀ := by
      intro u hu
      rw [hV, Finset.mem_filter] at hu
      exact hu.2
    rw [Finset.sum_congr rfl fun u hu => by rw [if_pos (hmemV u hu)]]
    -- (3) pointwise decomposition and the single `t₀`-term
    let t' : ↥(tmI (descS S w₀)) := descT (F := F) (w₀ := w₀) t₀ ht₀
    have ht'V : t' ∈ V := by
      rw [hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa only [t', descT_val] using ht₀⟩
    have hpoint : ∀ u ∈ V, (if u.1 = t₀.1 then Zl u.1 else -(μ u.1) * Zl u.1)
        = -((μ u.1) * Zl u.1) + (if u.1 = t₀.1 then Zl u.1 + μ u.1 * Zl u.1 else 0) := by
      intro u _
      by_cases h1 : u.1 = t₀.1
      · rw [if_pos h1, if_pos h1]; ring
      · rw [if_neg h1, if_neg h1]; ring
    rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have hsingle : (∑ u ∈ V, (if u.1 = t₀.1 then Zl u.1 + μ u.1 * Zl u.1 else 0))
        = Zl t₀.1 + μ t'.1 * Zl t'.1 := by
      have hft : (if t'.1 = t₀.1 then Zl t'.1 + μ t'.1 * Zl t'.1 else 0)
          = Zl t₀.1 + μ t'.1 * Zl t'.1 := by
        rw [show t'.1 = t₀.1 from by simp only [t', descT_val], if_pos rfl]
      have hsum : (∑ u ∈ V, (if u.1 = t₀.1 then Zl u.1 + μ u.1 * Zl u.1 else 0))
          = (if t'.1 = t₀.1 then Zl t'.1 + μ t'.1 * Zl t'.1 else 0) :=
        Finset.sum_eq_single
          (f := fun u : ↥(tmI (descS S w₀)) =>
            (if u.1 = t₀.1 then Zl u.1 + μ u.1 * Zl u.1 else 0)) t'
          (fun u _ hu => by
            rw [if_neg (fun hh => hu (Subtype.ext (by simp only [t', descT_val]; exact hh)))])
          (fun h => absurd ht'V h)
      exact hsum.trans hft
    rw [hsingle]
    -- the `μ`-value at `t'` is `lam t₀`
    have hμt' : μ t'.1 = lam t₀ := by
      have h := hμ t' (show tmWeight t'.1 = w₀ from ht₀)
      simp only [t', descT_val] at h
      exact h.trans (congrArg lam (Subtype.ext rfl))
    rw [hμt']
    -- (4) `hab` and the split of `W''`, then `hrel`
    rw [hab]
    have hW : (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀))
        = (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ t₀))
          ∪ {t₀} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · intro h
        by_cases h2 : t = t₀
        · exact Or.inr h2
        · exact Or.inl ⟨h, h2⟩
      · rintro (⟨h, -⟩ | rfl)
        · exact h
        · exact ht₀
    have hdisj : Disjoint
        (Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀ ∧ t ≠ t₀)) {t₀} := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      exact h.2 rfl
    rw [hW, Finset.sum_union hdisj, Finset.sum_singleton]
    rw [← hrel]
    rw [show t'.1 = t₀.1 from by simp only [t', descT_val]]
    ring
  -- ## conclude: apply `descent_relation` and convert back to the `↥(tmI S)`-indexing
  have hρ := descent_relation (F := F) (ω := ω) hγ0 hγ harch hq hω hωse hc hωfe
    hsm hSse hpos hQmem ht₀ hind hρmem hρ0 hρtop hval
  intro t ht hne
  set u : ↥(tmI (descS S w₀)) := ⟨t.1, mem_tmI_descS_of_mem_descW (mem_descW.mpr ⟨t, ht, rfl⟩)⟩
  have hu1 : u.1 = t.1 := rfl
  have hune : u ≠ descT (F := F) (w₀ := w₀) t₀ ht₀ := fun hh =>
    hne (Subtype.ext (hu1 ▸ Subtype.ext_iff.mp hh))
  have hres := hρ u (by rw [hu1]; exact ht) hune
  have hρu : ρ (some u) = -(μ u.1) := by
    simp only [ρ]
    rw [if_neg (fun hh => hne (Subtype.ext (hu1 ▸ hh))),
      if_pos (by rw [hu1]; exact ht)]
  rw [hρu, hμ u (by rw [hu1]; exact ht)] at hres
  simpa [hu1] using Subfield.neg_mem (ambK F) hres

end ZagierHoffmanPositiveChar
