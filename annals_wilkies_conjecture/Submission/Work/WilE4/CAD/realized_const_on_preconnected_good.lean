import Mathlib
import Submission.Work.WilE4.Poly
import Submission.Work.WilE4.CAD.type_local
import Submission.Work.WilE4.CAD.realized_of_tendsto_bdd_good
import Submission.Work.WilE4.CAD.realized_of_tendsto_unbdd_good

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec)

/-! ## Sequential limit of a realised sign vector along a sequence of good points

`type_local.lean` proves that the set of realised sign vectors is locally constant at a point `x`
where `Good P d` holds *eventually* near `x`.  Here we only know `Good` at the points of `C`
itself, so we re-run the limit argument with the pointwise hypotheses `Good P d x` (at the limit)
and `Good P d (a n)` (at the approximating points). -/

/-- Sequential closedness of the realised sign vector set, with `Good` assumed at the limit point
and at each point of the sequence. -/
theorem realized_of_tendsto_good {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m+1)) ℝ}
    {d : Fin k → ℕ} {x : Fin m → ℝ} (hgoodx : Good P d x)
    {a : ℕ → Fin m → ℝ} (ha : Tendsto a atTop (𝓝 x)) (hgoodn : ∀ n, Good P d (a n))
    {v : Fin k → SignType} (hv : ∀ n, realized P (a n) v) :
    realized P x v := by
  choose w hw using hv
  by_cases hbdd : ∃ M : ℝ, ∀ᶠ n in atTop, |w n| ≤ M
  · obtain ⟨M, hM⟩ := hbdd
    have hfreq : ∃ᶠ n in atTop, w n ∈ Set.Icc (-M) M :=
      (hM.mono fun n hn => abs_le.mp hn).frequently
    obtain ⟨w₀, _, φ, hφmono, hφlim⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (-M) M)).tendsto_subseq' hfreq
    exact realized_of_tendsto_bdd_good hgoodx (ha.comp hφmono.tendsto_atTop) hφlim
      (hφmono.tendsto_atTop.eventually (Filter.Eventually.of_forall hw))
  · push_neg at hbdd
    exact realized_of_tendsto_unbdd_good hgoodx ha hgoodn hw hbdd

/-- **Main step.**  If the non-degeneracy conditions hold at *every* point of a preconnected set
`C`, then the set of realised sign vectors is constant on `C`. -/
theorem realized_const_on_preconnected_good_q {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (d : Fin k → ℕ) (C : Set (Fin m → ℝ)) (hC : IsPreconnected C)
    (hdeg : ∀ x ∈ C, ∀ i, (q (P i) x).natDegree = d i)
    (hcop : ∀ x ∈ C, ∀ i j, i ≠ j → IsCoprime (q (P i) x) (q (P j) x))
    (hsq : ∀ x ∈ C, ∀ i, IsCoprime (q (P i) x) ((q (P i) x).derivative))
    (v : Fin k → SignType) :
    (∀ x ∈ C, realized P x v) ∨ (∀ x ∈ C, ¬ realized P x v) := by
  have hgood_at : ∀ x ∈ C, Good P d x := fun x hx => ⟨hdeg x hx, hcop x hx, hsq x hx⟩
  -- points of `C` at which `v` is realised form a relatively open set
  have keyU : ∀ x : Fin m → ℝ, x ∈ C ∩ {y | realized P y v} →
      ∃ T : Set (Fin m → ℝ), IsOpen T ∧ x ∈ T ∧ T ⊆ {y | realized P y v} := by
    intro x hx
    obtain ⟨V, hV, hV'⟩ := Filter.eventually_iff_exists_mem.mp
      (realized_nhds_of_realized (hgood_at x hx.1) hx.2)
    obtain ⟨t, htV, hto, hxt⟩ := mem_nhds_iff.mp hV
    exact ⟨t, hto, hxt, fun y hy => hV' y (htV hy)⟩
  -- the remaining points form a relatively open set as well (relative closedness of the first)
  have keyW : ∀ x : Fin m → ℝ, x ∈ C ∩ {y | ¬ realized P y v} →
      ∃ T : Set (Fin m → ℝ), IsOpen T ∧ x ∈ T ∧ T ⊆ {y | y ∈ C → ¬ realized P y v} := by
    intro x hx
    have hclosed : ∀ᶠ y in 𝓝 x, (y ∈ C → ¬ realized P y v) := by
      by_contra hcon
      obtain ⟨u, hu, huu⟩ := seq_extract (x₀ := x)
        (P := fun y => (y ∈ C → ¬ realized P y v)) hcon
      have huu' : ∀ n, u n ∈ C ∧ realized P (u n) v := fun n => by
        have h := not_imp.mp (huu n)
        exact ⟨h.1, Classical.not_not.mp h.2⟩
      exact hx.2 (realized_of_tendsto_good (hgood_at x hx.1) hu
        (fun n => hgood_at (u n) (huu' n).1) (fun n => (huu' n).2))
    obtain ⟨V, hV, hV'⟩ := Filter.eventually_iff_exists_mem.mp hclosed
    obtain ⟨t, htV, hto, hxt⟩ := mem_nhds_iff.mp hV
    exact ⟨t, hto, hxt, fun y hy => hV' y (htV hy)⟩
  -- assemble the two relative open sets as ambient open sets
  set U' : Set (Fin m → ℝ) := ⋃₀ {T : Set (Fin m → ℝ) |
      IsOpen T ∧ T ⊆ {y | realized P y v} ∧
        (∃ x, x ∈ C ∩ {y | realized P y v} ∧ x ∈ T)}
  set W' : Set (Fin m → ℝ) := ⋃₀ {T : Set (Fin m → ℝ) |
      IsOpen T ∧ T ⊆ {y | y ∈ C → ¬ realized P y v} ∧
        (∃ x, x ∈ C ∩ {y | ¬ realized P y v} ∧ x ∈ T)}
  have hU'open : IsOpen U' := isOpen_sUnion fun T hT => hT.1
  have hW'open : IsOpen W' := isOpen_sUnion fun T hT => hT.1
  have hU'sub : U' ⊆ {y | realized P y v} := by
    intro y hy
    obtain ⟨T, hT, hyT⟩ := Set.mem_sUnion.mp hy
    exact hT.2.1 hyT
  have hW'sub : W' ⊆ {y | y ∈ C → ¬ realized P y v} := by
    intro y hy
    obtain ⟨T, hT, hyT⟩ := Set.mem_sUnion.mp hy
    exact hT.2.1 hyT
  have hCU : C ∩ {y | realized P y v} ⊆ U' := by
    intro y hy
    obtain ⟨T, hTo, hyT, hTs⟩ := keyU y hy
    exact Set.mem_sUnion.mpr ⟨T, ⟨hTo, hTs, ⟨y, hy, hyT⟩⟩, hyT⟩
  have hCW : C ∩ {y | ¬ realized P y v} ⊆ W' := by
    intro y hy
    obtain ⟨T, hTo, hyT, hTs⟩ := keyW y hy
    exact Set.mem_sUnion.mpr ⟨T, ⟨hTo, hTs, ⟨y, hy, hyT⟩⟩, hyT⟩
  -- pass to the subspace `C`, where the two sets are clopen and cover `C`
  haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have hUCeq : (Subtype.val ⁻¹' U' : Set C) = {x : C | realized P x.1 v} := by
    ext x; constructor
    · intro hx; exact hU'sub hx
    · intro hx; exact hCU ⟨x.2, hx⟩
  have hWCeq : (Subtype.val ⁻¹' W' : Set C) = {x : C | ¬ realized P x.1 v} := by
    ext x; constructor
    · intro hx; exact hW'sub hx x.2
    · intro hx; exact hCW ⟨x.2, hx⟩
  have hUCopen : IsOpen (Subtype.val ⁻¹' U' : Set C) := hU'open.preimage continuous_subtype_val
  have hWCopen : IsOpen (Subtype.val ⁻¹' W' : Set C) := hW'open.preimage continuous_subtype_val
  have hdisj : Disjoint (Subtype.val ⁻¹' U' : Set C) (Subtype.val ⁻¹' W' : Set C) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [hUCeq] at hx
    rw [hWCeq] at hx'
    exact hx' hx
  have hsub : (Set.univ : Set C) ⊆ (Subtype.val ⁻¹' U' : Set C) ∪ (Subtype.val ⁻¹' W' : Set C) := by
    intro x _
    by_cases h : realized P x.1 v
    · left; rwa [hUCeq]
    · right; rwa [hWCeq]
  by_cases hne : ((Set.univ : Set C) ∩ (Subtype.val ⁻¹' U' : Set C)).Nonempty
  · left
    have h := IsPreconnected.subset_left_of_subset_union hUCopen hWCopen hdisj hsub hne
      (isPreconnected_univ : IsPreconnected (Set.univ : Set C))
    intro x hx
    have hx' : (⟨x, hx⟩ : C) ∈ (Subtype.val ⁻¹' U' : Set C) := h (Set.mem_univ _)
    rwa [hUCeq] at hx'
  · right
    have h : (Set.univ : Set C) ⊆ (Subtype.val ⁻¹' W' : Set C) := by
      intro x hx
      rcases hsub hx with h1 | h2
      · exact absurd ⟨x, Set.mem_univ x, h1⟩ hne
      · exact h2
    intro x hx
    have h2 : (⟨x, hx⟩ : C) ∈ (Subtype.val ⁻¹' W' : Set C) := h (Set.mem_univ _)
    rw [hWCeq] at h2
    exact h2

/-- **Realised sign vectors of a family of polynomials are constant on a preconnected set on which
the family is non-degenerate** (fixed degrees, no common roots between distinct members, each
member squarefree). -/
theorem realized_const_on_preconnected_good {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (d : Fin k → ℕ) (C : Set (Fin m → ℝ)) (hC : IsPreconnected C)
    (hdeg : ∀ x ∈ C, ∀ i : Fin k, (Work.WilE4.spec (P i) x).natDegree = d i)
    (hcop : ∀ x ∈ C, ∀ i j : Fin k, i ≠ j → IsCoprime (Work.WilE4.spec (P i) x) (Work.WilE4.spec (P j) x))
    (hsq : ∀ x ∈ C, ∀ i : Fin k, IsCoprime (Work.WilE4.spec (P i) x) ((Work.WilE4.spec (P i) x).derivative))
    (v : Fin k → SignType) :
    (∀ x ∈ C, ∃ t : ℝ, ∀ i : Fin k, SignType.sign ((Work.WilE4.spec (P i) x).eval t) = v i) ∨
      (∀ x ∈ C, ¬ ∃ t : ℝ, ∀ i : Fin k, SignType.sign ((Work.WilE4.spec (P i) x).eval t) = v i) := by
  exact realized_const_on_preconnected_good_q (fun i => MvPolynomial.rename (rot m) (P i)) d C hC
    (fun x hx i => hdeg x hx i) (fun x hx i j hij => hcop x hx i j hij) (fun x hx i => hsq x hx i) v

end Work.WilE4.CAD
