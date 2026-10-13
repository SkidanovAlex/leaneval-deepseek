/-
  Work.WilE2 — area E2.  The counting step of the Khovanskii–Rolle elimination.

  This module packages the geometric input of the elimination in the exact form the induction
  consumes.  Fix a `C²` map `V : ℝ^{m+1} → ℝ^m` whose zero set is compact and where the gradients
  are independent (so that the zero set is a compact `1`-manifold).  Let `X` be the cross-product
  field of `tangentField_exists`, characterised by

    `⟨X z, v⟩ = det [∇V_1(z), …, ∇V_m(z), v]`.

  If `g` is `C¹` with non-degenerate roots on the zero set and `ψ` agrees with `dg(X)` at those
  roots, then for every `δ > 0` which is smaller than `|ψ|` at every root, the roots are dominated
  by the points of the zero set where `ψ = δ`.

  The two results here are

  * `fderiv_crossField` : `dg(X)` computed with the cross-product field is the determinant of the
    matrix `[∇V_1, …, ∇V_m, ∇g]` — this is the function `ψ` of the paper;
  * `rolle_count_elimination` : the counting statement above, with a *prescribed* `δ`.  The
    freedom in `δ` is what lets the elimination choose `δ` generically (so that the points with
    `ψ = δ` are regular solutions of the new system) while keeping `δ` below `|ψ|` at the roots.
-/
import Mathlib
import Submission.Work.WilE2.rolle_count_level_curve
import Submission.Work.WilE2.tangentField_exists
import Submission.Work.WilE2.compact_level_curve_flow

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Set

/-! ## §1. The derivative of `g` along the cross-product field -/

/-- The cross-product field `crossField V z` is the vector of cofactors of the last column of
`tangMatrix V z`, so the derivative of a function `g` along it is the determinant
`det [∇V_1(z), …, ∇V_m(z), ∇g(z)]`. -/
theorem fderiv_crossField {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (g : (Fin (m + 1) → ℝ) → ℝ) (z : Fin (m + 1) → ℝ) :
    fderiv ℝ g z (crossField V z) =
      (tangMatrix V z (fun i => fderiv ℝ g z (Pi.single i 1))).det := by
  rw [← crossField_det]
  exact clm_eq_sum_single (fderiv ℝ g z) (crossField V z)

/-! ## §2. Counting with a prescribed level `δ` -/

/-- **Khovanskii–Rolle counting, prescribed `δ`.**  Under the sweep hypothesis (the zero set of
`V` is swept by periodic integral curves of `X`), given `δ > 0` strictly below `|ψ|` at every
root of `g` on the zero set, every finite set of roots is dominated by a finite set of points of
the zero set where `ψ = δ`.  This is `rolle_count_level_curve` with the level `δ` chosen in
advance. -/
theorem rolle_count_level_curve_at {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ))
    (X : (Fin m → ℝ) → (Fin m → ℝ)) (g ψ : (Fin m → ℝ) → ℝ)
    (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X) (hg : ContDiff ℝ 1 g) (hψc : Continuous ψ)
    (hC : IsCompact {z | V z = 0})
    (hX0 : ∀ z, V z = 0 → X z ≠ 0)
    (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0)
    (hsweep : ∀ z, V z = 0 → ∃ (T : ℝ) (γ : ℝ → Fin m → ℝ), 0 < T ∧ γ 0 = z ∧
        (∀ t, HasDerivAt γ (X (γ t)) t) ∧ (∀ t, γ (t + T) = γ t) ∧
        Set.range γ = connectedComponentIn {z | V z = 0} z)
    (hpsi : ∀ z, V z = 0 → g z = 0 → ψ z = fderiv ℝ g z (X z))
    (hnd : ∀ z, V z = 0 → g z = 0 → fderiv ℝ g z (X z) ≠ 0)
    (δ : ℝ) (hδpos : 0 < δ) (hδlt : ∀ z, V z = 0 → g z = 0 → δ < |ψ z|) :
    ∀ s : Finset (Fin m → ℝ), (∀ z ∈ s, V z = 0 ∧ g z = 0) →
      ∃ t : Finset (Fin m → ℝ), (∀ z ∈ t, V z = 0 ∧ ψ z = δ) ∧ s.card ≤ t.card := by
  classical
  intro s hs
  let cf : (Fin m → ℝ) → Set (Fin m → ℝ) :=
    fun z => connectedComponentIn {z' | V z' = 0} z
  set sc : Finset (Set (Fin m → ℝ)) := s.image cf with hsc
  have hpiece : ∀ C ∈ sc, ∃ t : Finset (Fin m → ℝ),
      (∀ z ∈ t, V z = 0 ∧ ψ z = δ) ∧ (∀ z ∈ t, z ∈ C) ∧
      (s.filter (fun z => z ∈ C)).card ≤ t.card := by
    intro C hC
    obtain ⟨z₀, hz₀s, hz₀eq⟩ := Finset.mem_image.mp hC
    subst hz₀eq
    have hz₀V : V z₀ = 0 := (hs z₀ hz₀s).1
    have hsfil : ∀ z ∈ s.filter (fun z => z ∈ cf z₀),
        V z = 0 ∧ g z = 0 ∧ z ∈ connectedComponentIn {z' | V z' = 0} z₀ := by
      intro z hz
      rw [Finset.mem_filter] at hz
      exact ⟨(hs z hz.1).1, (hs z hz.1).2, hz.2⟩
    obtain ⟨t, ht1, ht2, ht3⟩ :=
      level_curve_component_count V X g ψ hV hX hg hψc hX0 hsweep hpsi hnd δ hδpos hδlt
        z₀ hz₀V (s.filter (fun z => z ∈ cf z₀)) hsfil
    exact ⟨t, ht1, ht2, ht3⟩
  let piece : Set (Fin m → ℝ) → Finset (Fin m → ℝ) :=
    fun C => if h : C ∈ sc then (hpiece C h).choose else ∅
  have piece_spec : ∀ C ∈ sc, (∀ z ∈ piece C, V z = 0 ∧ ψ z = δ) ∧
      (∀ z ∈ piece C, z ∈ C) ∧ (s.filter (fun z => z ∈ C)).card ≤ (piece C).card := by
    intro C hC
    have h := (hpiece C hC).choose_spec
    have hpc : piece C = (hpiece C hC).choose := by
      simp only [piece]; exact dif_pos hC
    rw [hpc]
    exact h
  have hdisj : (sc : Set (Set (Fin m → ℝ))).PairwiseDisjoint piece := by
    intro A hA B hB hne
    change Disjoint (piece A) (piece B)
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hzA' : z ∈ A := (piece_spec A hA).2.1 z hzA
    have hzB' : z ∈ B := (piece_spec B hB).2.1 z hzB
    obtain ⟨a, ha, hAeq⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, hBeq⟩ := Finset.mem_image.mp hB
    have hza : z ∈ cf a := hAeq ▸ hzA'
    have hzb : z ∈ cf b := hBeq ▸ hzB'
    refine hne ?_
    rw [← hAeq, ← hBeq]
    exact (connectedComponentIn_eq hza).trans (connectedComponentIn_eq hzb).symm
  refine ⟨sc.disjiUnion piece hdisj, ?_, ?_⟩
  · intro z hz
    obtain ⟨C, hC, hzC⟩ := Finset.mem_disjiUnion.mp hz
    exact (piece_spec C hC).1 z hzC
  · rw [Finset.card_disjiUnion]
    have hsum : (∑ C ∈ sc, (s.filter (fun z => z ∈ C)).card) = s.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := cf) (s := s) (t := sc)
        (fun z hz => Finset.mem_image_of_mem cf hz)
      rw [hfib]
      refine Finset.sum_congr rfl (fun C hC => ?_)
      congr 1
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hzs, hzC⟩
        obtain ⟨a, ha, hAeq⟩ := Finset.mem_image.mp hC
        have hza : z ∈ cf a := hAeq ▸ hzC
        exact ⟨hzs, hAeq ▸ (connectedComponentIn_eq hza).symm⟩
      · rintro ⟨hzs, hzf⟩
        exact ⟨hzs, hzf ▸ mem_connectedComponentIn (hs z hzs).1⟩
    calc s.card = ∑ C ∈ sc, (s.filter (fun z => z ∈ C)).card := hsum.symm
      _ ≤ ∑ C ∈ sc, (piece C).card := Finset.sum_le_sum (fun C hC => (piece_spec C hC).2.2)

/-! ## §3. The elimination form: the cross-product field is fixed, so its properties are
available to callers. -/

/-- **The counting step of the elimination.**  With `X` the cross-product field of `V`, the
hypotheses of `rolle_count_level_curve_at` reduce to: `V` is `C²` with compact zero set, the
gradients of `V` are independent on it, and `ψ` agrees with `dg(X)` at the roots. -/
theorem rolle_count_elimination {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ))
    (g ψ : (Fin (m + 1) → ℝ) → ℝ)
    (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 1 g) (hψc : Continuous ψ)
    (hC : IsCompact {z | V z = 0})
    (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => V w a) z))
    (hpsi : ∀ z, V z = 0 → g z = 0 → ψ z = fderiv ℝ g z (crossField V z))
    (hnd : ∀ z, V z = 0 → g z = 0 → fderiv ℝ g z (crossField V z) ≠ 0)
    (δ : ℝ) (hδpos : 0 < δ) (hδlt : ∀ z, V z = 0 → g z = 0 → δ < |ψ z|) :
    ∀ s : Finset (Fin (m + 1) → ℝ), (∀ z ∈ s, V z = 0 ∧ g z = 0) →
      ∃ t : Finset (Fin (m + 1) → ℝ), (∀ z ∈ t, V z = 0 ∧ ψ z = δ) ∧ s.card ≤ t.card := by
  have hX : ContDiff ℝ 1 (crossField V) := contDiff_crossField V hV
  have hX0 : ∀ z, V z = 0 → crossField V z ≠ 0 := fun z hz =>
    crossField_ne_zero_of_li V z (linearIndependent_tangGrad V z (hgrad z hz))
  have htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (crossField V z) = 0 :=
    fun z _ i => tangGrad_apply_crossField V z i
  have hsweep := compact_level_curve_flow V (crossField V) (hV.of_le (by norm_num)) hX hC
    hgrad hX0 htan
  refine rolle_count_level_curve_at V (crossField V) g ψ (hV.of_le (by norm_num)) hX hg hψc
    hC hX0 htan (fun z hz => ?_) hpsi hnd δ hδpos hδlt
  obtain ⟨T, γ, hT, hγ0, hder, hVγ, hper, hrange⟩ := hsweep z hz
  exact ⟨T, γ, hT, hγ0, hder, hper, hrange⟩

end Work.WilE2
