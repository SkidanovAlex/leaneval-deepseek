import Mathlib
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.hmidCC
import Submission.Work.Mostow.exists_min_circum
import Submission.Work.Mostow.image_closure_zpowOrbit

/-!
# An isometry of `ℍⁿ` with bounded orbit has a fixed point

This is the "elliptic case" of the classification of isometries of hyperbolic space: an isometry
of `ℍⁿ` whose orbit of some point is bounded must fix a point of `ℍⁿ`.

The proof is a circumcentre argument, carried out in the hyperboloid chart `E n`:

* `O = {g^m • u₀ | m : ℤ}` is the full cyclic orbit of `u₀` (two-sided, so that it is invariant
  under `g` without any case distinction) and `K = closure O`; the boundedness hypothesis makes
  `K` compact.
* `circRad K x = sSup ((fun v => hdist x v) '' K)` is the circumradius function of `K`; it is
  continuous and coercive, so it attains a minimum at some point `c` (`exists_min_circum`).
  Since `g '' K = K`, the point `g • c` is again a minimiser.
* If `g • c ≠ c`, let `m` be the hyperbolic midpoint of `c` and `g • c`.  Writing
  `ρ = circRad K c` and using the midpoint identity `hmidCC`
  `cc m v = (cc c v + cc (g • c) v) / (2 cosh (hdist c (g • c) / 2))`,
  together with the bounds `cc c v ≤ cosh ρ`, `cc (g • c) v ≤ cosh ρ` valid for all `v ∈ K`,
  one gets `hdist m v ≤ arcosh (cosh ρ / cosh (hdist c (g • c) / 2)) < ρ` for every `v ∈ K`,
  so that `circRad K m < ρ`, contradicting the minimality of `c`.

Hence `g • c = c`.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The circumradius function -/

/-- The least upper bound of the hyperbolic distances from `x` to the points of `K`. -/
def circRad (K : Set (E n)) (x : E n) : ℝ := sSup ((fun v : E n => hdist x v) '' K)

/-- A hyperbolic ball containing `K` bounds the distances from any `x` to `K`. -/
lemma bddAbove_hdist_image (hI : HypIsometryProp n) {K : Set (E n)} {M : ℝ}
    (hM : ∀ v ∈ K, hdist 0 v ≤ M) (x : E n) :
    BddAbove ((fun v : E n => hdist x v) '' K) := by
  have hdtri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w := hI.2.2.2.1
  refine ⟨hdist x 0 + M, ?_⟩
  rintro b ⟨v, hv, rfl⟩
  calc hdist x v ≤ hdist x 0 + hdist 0 v := hdtri x 0 v
    _ ≤ hdist x 0 + M := by linarith [hM v hv]

/-- The distance to a point of `K` is at most the circumradius. -/
lemma hdist_le_circRad (hI : HypIsometryProp n) {K : Set (E n)} {M : ℝ}
    (hM : ∀ v ∈ K, hdist 0 v ≤ M) {x v : E n} (hv : v ∈ K) :
    hdist x v ≤ circRad K x :=
  le_csSup (bddAbove_hdist_image hI hM x) ⟨v, hv, rfl⟩

/-- A uniform bound on the distances to `K` bounds the circumradius. -/
lemma circRad_le {K : Set (E n)} {x : E n} {b : ℝ} (hKn : K.Nonempty)
    (h : ∀ v ∈ K, hdist x v ≤ b) : circRad K x ≤ b :=
  csSup_le (hKn.image (fun v : E n => hdist x v))
    (by rintro b' ⟨v, hv, rfl⟩; exact h v hv)

/-- The circumradius of a nonempty set is nonnegative. -/
lemma circRad_nonneg (hI : HypIsometryProp n) {K : Set (E n)} {M : ℝ}
    (hM : ∀ v ∈ K, hdist 0 v ≤ M) (hKn : K.Nonempty) (x : E n) : 0 ≤ circRad K x := by
  have hdnn : ∀ u v : E n, 0 ≤ hdist u v := hI.1
  obtain ⟨v, hv⟩ := hKn
  exact le_trans (hdnn x v) (hdist_le_circRad hI hM hv)

/-! ## The main theorem -/

theorem boundedOrbitFixed (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (u₀ : E n)
    (hbdd : ∃ R : ℝ, ∀ m : ℕ, hdist u₀ ((g ^ m) • u₀) ≤ R) :
    ∃ u : E n, g • u = u := by
  obtain ⟨R, hR⟩ := hbdd
  have hdnn : ∀ u v : E n, 0 ≤ hdist u v := hI.1
  have hdsym : ∀ u v : E n, hdist u v = hdist v u := hI.2.1
  have hdzero : ∀ u v : E n, hdist u v = 0 ↔ u = v := hI.2.2.1
  have hdtri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w := hI.2.2.2.1
  have hdcompact : ∀ (u : E n) (r : ℝ), IsCompact {v : E n | hdist u v ≤ r} := hI.2.2.2.2.2.1
  have hisom : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v :=
    hI.2.2.2.2.2.2.1
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hcontAct : Continuous (fun p : PO n 1 × E n => p.1 • p.2) := hA.2.2.2.2.2.2.1
  -- the two-sided orbit and its closure
  set O : Set (E n) := Set.range (fun m : ℤ => (g ^ m) • u₀) with hO
  have hu₀O : u₀ ∈ O := by
    refine ⟨0, ?_⟩
    show (g ^ (0 : ℤ)) • u₀ = u₀
    rw [zpow_zero, hone]
  have hObdd : ∀ m : ℤ, hdist u₀ ((g ^ m) • u₀) ≤ R := by
    intro m
    rcases le_or_gt 0 m with hm | hm
    · rw [show g ^ m = g ^ m.toNat from by rw [← zpow_natCast, Int.toNat_of_nonneg hm]]
      exact hR m.toNat
    · have hk : (0 : ℤ) < -m := by omega
      have hcomp : g ^ (-m) • ((g ^ m) • u₀) = u₀ := by
        rw [← hmul, ← zpow_add, neg_add_cancel, zpow_zero, hone]
      have hnat : g ^ (-m) = g ^ ((-m).toNat) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hk.le]
      calc hdist u₀ ((g ^ m) • u₀)
          = hdist (g ^ (-m) • u₀) (g ^ (-m) • ((g ^ m) • u₀)) :=
            (hisom (g ^ (-m)) u₀ ((g ^ m) • u₀)).symm
        _ = hdist (g ^ (-m) • u₀) u₀ := by rw [hcomp]
        _ = hdist u₀ (g ^ (-m) • u₀) := hdsym _ _
        _ = hdist u₀ (g ^ ((-m).toNat) • u₀) := by rw [hnat]
        _ ≤ R := hR _
  set K : Set (E n) := closure O with hK
  have hOsub : O ⊆ {v : E n | hdist u₀ v ≤ R} := by
    rintro v ⟨m, rfl⟩
    exact hObdd m
  have hballclosed : IsClosed {v : E n | hdist u₀ v ≤ R} := (hdcompact u₀ R).isClosed
  have hKsub' : K ⊆ {v : E n | hdist u₀ v ≤ R} := by
    rw [hK]
    exact (hballclosed.closure_subset_iff).mpr hOsub
  have hKcomp : IsCompact K := by
    rw [hK]
    exact (hdcompact u₀ R).of_isClosed_subset isClosed_closure
      ((hballclosed.closure_subset_iff).mpr hOsub)
  have hKne : K.Nonempty := by
    rw [hK]
    exact ⟨u₀, subset_closure hu₀O⟩
  have hKbdd : ∀ v ∈ K, hdist 0 v ≤ hdist 0 u₀ + R := by
    intro v hv
    have hv1 : hdist u₀ v ≤ R := hKsub' hv
    calc hdist 0 v ≤ hdist 0 u₀ + hdist u₀ v := hdtri 0 u₀ v
      _ ≤ hdist 0 u₀ + R := by linarith
  -- the closure of the two-sided orbit is exactly `g`-invariant
  have hφK : (fun u : E n => g • u) '' K = K := by
    rw [hK, hO]
    exact image_closure_zpowOrbit n hA g u₀
  -- a minimiser of the circumradius, and the fact that `g • c` is again one
  obtain ⟨c, hcmin⟩ := exists_min_circum n hI hKcomp hKne
  have hcmin' : ∀ x : E n, circRad K c ≤ circRad K x := fun x => hcmin x
  have hFgc : circRad K (g • c) = circRad K c := by
    unfold circRad
    congr 1
    apply Set.Subset.antisymm
    · rintro b ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hwv⟩ : v ∈ (fun u : E n => g • u) '' K := hφK.symm ▸ hv
      have hwv' : g • w = v := hwv
      refine ⟨w, hw, ?_⟩
      show hdist c w = hdist (g • c) v
      rw [← hisom g c w, hwv']
    · rintro b ⟨v, hv, rfl⟩
      exact ⟨g • v, hφK ▸ Set.mem_image_of_mem (fun u : E n => g • u) hv, hisom g c v⟩
  -- conclude
  by_cases hfix : g • c = c
  · exact ⟨c, hfix⟩
  · exfalso
    have hne' : c ≠ g • c := fun h => hfix h.symm
    have hposd : 0 < hdist c (g • c) :=
      lt_of_le_of_ne (hdnn c (g • c)) (fun h0 => hne' ((hdzero c (g • c)).mp h0.symm))
    have hρnn : 0 ≤ circRad K c := circRad_nonneg hI hKbdd hKne c
    -- bounds on `cc` over the compact set `K`
    have hcc1 : ∀ v ∈ K, Hyper.cc c v ≤ Real.cosh (circRad K c) := by
      intro v hv
      have h1 : hdist c v ≤ circRad K c := hdist_le_circRad hI hKbdd hv
      calc Hyper.cc c v = Real.cosh (hdist c v) := (cosh_hdist c v).symm
        _ ≤ Real.cosh (circRad K c) := by
            rw [Real.cosh_le_cosh, abs_of_nonneg (hdnn c v), abs_of_nonneg hρnn]
            exact h1
    have hcc2 : ∀ v ∈ K, Hyper.cc (g • c) v ≤ Real.cosh (circRad K c) := by
      intro v hv
      have h1 : hdist (g • c) v ≤ circRad K c := by
        rw [← hFgc]
        exact hdist_le_circRad hI hKbdd hv
      calc Hyper.cc (g • c) v = Real.cosh (hdist (g • c) v) := (cosh_hdist (g • c) v).symm
        _ ≤ Real.cosh (circRad K c) := by
            rw [Real.cosh_le_cosh, abs_of_nonneg (hdnn (g • c) v), abs_of_nonneg hρnn]
            exact h1
    -- the midpoint `hmid c (g • c)` is strictly closer to every point of `K`
    have hDpos : 0 < Real.cosh (circRad K c) / Real.cosh (hdist c (g • c) / 2) :=
      div_pos (Real.cosh_pos _) (Real.cosh_pos _)
    have hDlt : Real.cosh (circRad K c) / Real.cosh (hdist c (g • c) / 2) <
        Real.cosh (circRad K c) := by
      rw [div_lt_iff₀ (Real.cosh_pos _)]
      have h1 : 1 < Real.cosh (hdist c (g • c) / 2) := by
        rw [Real.one_lt_cosh]
        exact ne_of_gt (by linarith)
      nlinarith [Real.cosh_pos (circRad K c)]
    have hccm : ∀ v ∈ K, Hyper.cc (hmid c (g • c)) v ≤
        Real.cosh (circRad K c) / Real.cosh (hdist c (g • c) / 2) := by
      intro v hv
      rw [hmidCC n c (g • c) v]
      have hstep : (Hyper.cc c v + Hyper.cc (g • c) v) / (2 * Real.cosh (hdist c (g • c) / 2)) ≤
          (Real.cosh (circRad K c) + Real.cosh (circRad K c)) /
            (2 * Real.cosh (hdist c (g • c) / 2)) :=
        div_le_div_of_nonneg_right (add_le_add (hcc1 v hv) (hcc2 v hv)) (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      field_simp
      ring
    have harcosh_lt : Real.arcosh (Real.cosh (circRad K c) /
        Real.cosh (hdist c (g • c) / 2)) < circRad K c := by
      have h1 : Real.arcosh (Real.cosh (circRad K c) / Real.cosh (hdist c (g • c) / 2)) <
          Real.arcosh (Real.cosh (circRad K c)) :=
        (Real.arcosh_lt_arcosh hDpos (Real.cosh_pos _)).mpr hDlt
      rwa [Real.arcosh_cosh hρnn] at h1
    have hFm : circRad K (hmid c (g • c)) ≤
        Real.arcosh (Real.cosh (circRad K c) / Real.cosh (hdist c (g • c) / 2)) := by
      apply circRad_le hKne
      intro v hv
      exact (Real.arcosh_le_arcosh
        (lt_of_lt_of_le zero_lt_one (one_le_cosh_hdist (hmid c (g • c)) v)) hDpos).mpr
        (hccm v hv)
    have hmin := hcmin' (hmid c (g • c))
    linarith

end

end Work.Mostow
