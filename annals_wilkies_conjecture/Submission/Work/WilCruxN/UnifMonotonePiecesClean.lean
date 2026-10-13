import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilCrux.signSets_mem
import Submission.Work.WilCrux.badLocus_card_bound
import Submission.Work.WilCrux.monotone_or_antitone_of_deriv_sign

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
open Classical
open scoped Topology

namespace Work.WilCruxN

open Work.WilCrux

open WilkiesDesign

/-!
## The `Fin 1`-bookkeeping

The one-dimensional space of the sharp-o-minimality axioms is `Fin 1 → ℝ`; the lemmas below
transfer a set of reals back and forth along the (unique) coordinate.
-/

/-- The `Fin 1`-point with value `t`. -/
def pt1 (t : ℝ) : Fin 1 → ℝ := fun _ => t

@[simp] lemma pt1_apply (t : ℝ) : pt1 t 0 = t := rfl

lemma eq_pt1 (z : Fin 1 → ℝ) : z = pt1 (z 0) := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

/-- The projection of a subset of `ℝ¹ = Fin 1 → ℝ` to `ℝ`. -/
def drop1 (c : Set (Fin 1 → ℝ)) : Set ℝ := (fun z : Fin 1 → ℝ => z 0) '' c

/-- The right endpoint of a piece. -/
def sSupDrop (c : Set (Fin 1 → ℝ)) : ℝ := sSup (drop1 c)

lemma mem_drop1 {c : Set (Fin 1 → ℝ)} {u : ℝ} : u ∈ drop1 c ↔ pt1 u ∈ c := by
  constructor
  · rintro ⟨z, hz, hzu⟩
    have h : z = pt1 u := by
      funext i
      rw [Subsingleton.elim i 0]
      exact hzu
    rwa [h] at hz
  · intro h
    exact ⟨pt1 u, h, rfl⟩

lemma ordConnected_drop1 {c : Set (Fin 1 → ℝ)} (hc : IsPreconnected c) :
    (drop1 c).OrdConnected :=
  isPreconnected_iff_ordConnected.mp (hc.image _ (continuous_apply 0).continuousOn)

/-!
## The crux: sign constancy off the piece-endpoints
-/

/-- **Sign constancy.**  Let `d : ℝ → ℝ`.  Suppose `{d > 0}` and `{d < 0}` are each covered by a
finite family of preconnected pieces of `ℝ¹ = Fin 1 → ℝ`, and let `brk` contain the right
endpoint of every piece.  Then on every interval `(s,t)` whose interior avoids `brk`, the function
`d` has a constant sign: it is either `≥ 0` everywhere or `≤ 0` everywhere.

Proof.  Suppose `d` takes a negative value at `u₀ ∈ (s,t)` and a positive value at `u₁ ∈ (s,t)`.
If `u₀ < u₁`, take a piece `Q` of `{d < 0}` through `u₀`.  Its image `drop1 Q` is an interval
containing `u₀` and not `u₁` (a point of `Q` is a point of `{d < 0}`), so it is bounded above by
`u₁`; hence its right endpoint lies in `[u₀,u₁] ⊆ (s,t)`, contradicting the avoidance of `brk`.
If `u₁ < u₀`, the same argument with a piece of `{d > 0}` through `u₁` applies. -/
lemma signConst_of_pieces (d : ℝ → ℝ) (sp sn : Finset (Set (Fin 1 → ℝ))) (brk : Finset ℝ)
    (hsp : ({z : Fin 1 → ℝ | 0 < d (z 0)} : Set (Fin 1 → ℝ))
      = ⋃₀ (sp : Set (Set (Fin 1 → ℝ))))
    (hpconn : ∀ c ∈ sp, IsPreconnected c)
    (hsn : ({z : Fin 1 → ℝ | d (z 0) < 0} : Set (Fin 1 → ℝ))
      = ⋃₀ (sn : Set (Set (Fin 1 → ℝ))))
    (hnconn : ∀ c ∈ sn, IsPreconnected c)
    (hbrk : ∀ c ∈ sp ∪ sn, sSupDrop c ∈ brk)
    (s t : ℝ) (hav : ∀ u ∈ Set.Ioo s t, u ∉ brk) :
    (∀ u ∈ Set.Ioo s t, 0 ≤ d u) ∨ (∀ u ∈ Set.Ioo s t, d u ≤ 0) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  push Not at h1 h2
  obtain ⟨u₀, hu₀J, hu₀⟩ := h1
  obtain ⟨u₁, hu₁J, hu₁⟩ := h2
  rcases lt_trichotomy u₀ u₁ with hlt | heq | hgt
  · -- A negative point below a positive point: the negative piece through `u₀` ends in `(s,t)`.
    have hmemA : pt1 u₀ ∈ ({z : Fin 1 → ℝ | d (z 0) < 0} : Set (Fin 1 → ℝ)) := hu₀
    rw [hsn] at hmemA
    obtain ⟨Q, hQ, hQmem⟩ := Set.mem_sUnion.mp hmemA
    have hQord : (drop1 Q).OrdConnected := ordConnected_drop1 (hnconn Q hQ)
    have hu₀Q : u₀ ∈ drop1 Q := mem_drop1.mpr hQmem
    have hnotu₁ : u₁ ∉ drop1 Q := by
      intro h
      have hQ₁ : pt1 u₁ ∈ Q := mem_drop1.mp h
      have hmem : pt1 u₁ ∈ ({z : Fin 1 → ℝ | d (z 0) < 0} : Set (Fin 1 → ℝ)) := by
        rw [hsn]
        exact Set.mem_sUnion.mpr ⟨Q, hQ, hQ₁⟩
      exact absurd hmem (not_lt.mpr hu₁.le)
    have hupper : ∀ q ∈ drop1 Q, q ≤ u₁ := by
      intro q hq
      by_contra hq'
      have : u₁ ∈ Set.Icc u₀ q := ⟨hlt.le, le_of_lt (not_le.mp hq')⟩
      exact hnotu₁ (hQord.out hu₀Q hq this)
    have hub : sSup (drop1 Q) ≤ u₁ := csSup_le ⟨u₀, hu₀Q⟩ hupper
    have hlb : u₀ ≤ sSup (drop1 Q) := le_csSup ⟨u₁, hupper⟩ hu₀Q
    have hmemJ : sSup (drop1 Q) ∈ Set.Ioo s t :=
      ⟨lt_of_lt_of_le hu₀J.1 hlb, lt_of_le_of_lt hub hu₁J.2⟩
    exact hav _ hmemJ (hbrk Q (Finset.mem_union.mpr (Or.inr hQ)))
  · exact absurd (heq ▸ hu₁) (not_lt.mpr hu₀.le)
  · -- A positive point below a negative point: the positive piece through `u₁` ends in `(s,t)`.
    have hmemA : pt1 u₁ ∈ ({z : Fin 1 → ℝ | 0 < d (z 0)} : Set (Fin 1 → ℝ)) := hu₁
    rw [hsp] at hmemA
    obtain ⟨P, hP, hPmem⟩ := Set.mem_sUnion.mp hmemA
    have hPord : (drop1 P).OrdConnected := ordConnected_drop1 (hpconn P hP)
    have hu₁P : u₁ ∈ drop1 P := mem_drop1.mpr hPmem
    have hnotu₀ : u₀ ∉ drop1 P := by
      intro h
      have hP₀ : pt1 u₀ ∈ P := mem_drop1.mp h
      have hmem : pt1 u₀ ∈ ({z : Fin 1 → ℝ | 0 < d (z 0)} : Set (Fin 1 → ℝ)) := by
        rw [hsp]
        exact Set.mem_sUnion.mpr ⟨P, hP, hP₀⟩
      exact absurd hmem (not_lt.mpr hu₀.le)
    have hupper : ∀ q ∈ drop1 P, q ≤ u₀ := by
      intro q hq
      by_contra hq'
      have : u₀ ∈ Set.Icc u₁ q := ⟨hgt.le, le_of_lt (not_le.mp hq')⟩
      exact hnotu₀ (hPord.out hu₁P hq this)
    have hub : sSup (drop1 P) ≤ u₀ := csSup_le ⟨u₁, hu₁P⟩ hupper
    have hlb : u₁ ≤ sSup (drop1 P) := le_csSup ⟨u₀, hupper⟩ hu₁P
    have hmemJ : sSup (drop1 P) ∈ Set.Ioo s t :=
      ⟨lt_of_lt_of_le hu₁J.1 hlb, lt_of_le_of_lt hub hu₀J.2⟩
    exact hav _ hmemJ (hbrk P (Finset.mem_union.mpr (Or.inl hP)))

/-- **N4c4 (uniform monotonicity pieces for definable functions of one variable).**  There is a
bound `K`, depending only on the format `F` and degree `D`, such that every definable
`h : ℝ → ℝ` with `graphOf h ∈ Ω F D 2` is differentiable off, and has monotone or antitone
restrictions between, at most `K` "break points" — i.e. `h` is monotone on every interval whose
interior avoids the finite set `brk`.

Proof.  The two sign loci `A⁺ := {z : Fin 1 → ℝ | 0 < deriv h (z 0)}` and
`A⁻ := {z | deriv h (z 0) < 0}` are `Ω`-definable with format and degree depending only on `S`
and `F` (`signSets_mem`, from `derivGraph_mem` — the `ε`-`δ` derivative set of a definable graph
— plus the half-spaces `posHalf`/`negHalf` and a projection).  `S.comps` writes each of them as
a finite union of preconnected pieces, with `≤ p.eval (b.eval D)` pieces for a polynomial `p`
depending only on `S` and `F`.  The non-`C¹` locus of `h` is finite with a cardinality bounded
uniformly in `h` by a function of `S, F, D` (`badLocus_card_bound`: `jointBad_mem` gives
`Ω`-definability, `G1_generic_smooth_proved` gives empty interior, and the preconnected pieces
supplied by `S.comps` are then subsingletons).

Take `brk` to be the union of the bounded-cardinality set `Bb` of non-`C¹` points with the right
endpoints `sSup (drop1 c)` of all the pieces `c` of `A⁺` and of `A⁻`; this is
`≤ Kb + 2 * p.eval (b.eval D) + 2` points.  Off `brk`, `h` is `C¹`, hence differentiable.  On an
interval `(s,t)` whose interior avoids `brk`, the derivative cannot change sign: if `deriv h` were
negative at `u₀ ∈ (s,t)` and positive at `u₁ ∈ (s,t)`, then the piece of `A⁻` through `u₀`
(resp. of `A⁺` through `u₁`) according as `u₀ < u₁` (resp. `u₁ < u₀`) is a preconnected set whose
image in `ℝ` is an interval containing the corresponding point and avoiding the other one; its
right endpoint therefore lies in `[min u₀ u₁, max u₀ u₁] ⊆ (s,t)`, contradicting the avoidance of
`brk` (`signConst_of_pieces`).  Hence `deriv h` is `≥ 0` everywhere or `≤ 0` everywhere on
`(s,t)`, and `monotone_or_antitone_of_deriv_sign` (the mean value theorem) concludes. -/
theorem UnifMonotonePieces (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (F D : ℕ) :
    ∃ K : ℕ, ∀ h : ℝ → ℝ, WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => h (x 0)) ∈ S.Ω F D 2 →
      ∃ brk : Finset ℝ, brk.card ≤ K ∧ (∀ s, s ∉ brk → DifferentiableAt ℝ h s) ∧
        ∀ s t : ℝ, s < t → (∀ u ∈ Set.Ioo s t, u ∉ brk) →
          MonotoneOn h (Set.Ioo s t) ∨ AntitoneOn h (Set.Ioo s t) := by
  obtain ⟨a, b, hsign⟩ := signSets_mem S F
  obtain ⟨p, hp⟩ := S.comps a
  obtain ⟨Kb, hbad⟩ := badLocus_card_bound S hcd F D
  refine ⟨Kb + 2 * p.eval (b.eval D) + 2, ?_⟩
  intro h hg
  obtain ⟨hpos_mem, hneg_mem⟩ := hsign D h hg
  obtain ⟨sp, hsp_card, hsp_conn, hsp_eq⟩ := hp (b.eval D) _ hpos_mem
  obtain ⟨sn, hsn_card, hsn_conn, hsn_eq⟩ := hp (b.eval D) _ hneg_mem
  obtain ⟨Bb, hBb_card, hBb_good⟩ := hbad h hg
  refine ⟨Bb ∪ sp.image sSupDrop ∪ sn.image sSupDrop, ?_, ?_, ?_⟩
  · -- the cardinality of the break set
    have hspc : (sp.image sSupDrop).card ≤ p.eval (b.eval D) :=
      le_trans Finset.card_image_le hsp_card
    have hsnc : (sn.image sSupDrop).card ≤ p.eval (b.eval D) :=
      le_trans Finset.card_image_le hsn_card
    have h1 := Finset.card_union_le (Bb ∪ sp.image sSupDrop) (sn.image sSupDrop)
    have h2 := Finset.card_union_le Bb (sp.image sSupDrop)
    omega
  · -- differentiability off the break set
    intro x hx
    have hxBb : x ∉ Bb := fun hmem =>
      hx (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hmem))))
    exact (hBb_good x hxBb).differentiableAt (by norm_num)
  · -- monotonicity or antitonicity on any interval avoiding the break set
    intro s t hst hav
    have havBb : ∀ u ∈ Set.Ioo s t, u ∉ Bb := fun u hu hmem =>
      hav u hu (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hmem))))
    have hbrk : ∀ c ∈ sp ∪ sn, sSupDrop c ∈ Bb ∪ sp.image sSupDrop ∪ sn.image sSupDrop := by
      intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_image_of_mem sSupDrop hc))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem sSupDrop hc))
    have hconst := signConst_of_pieces (deriv h) sp sn
      (Bb ∪ sp.image sSupDrop ∪ sn.image sSupDrop) hsp_eq hsp_conn hsn_eq hsn_conn hbrk s t hav
    exact monotone_or_antitone_of_deriv_sign h
      (fun u hu => (hBb_good u (havBb u hu)).differentiableAt (by norm_num)) hconst

end Work.WilCruxN
