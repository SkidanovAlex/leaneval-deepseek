import Mathlib
import Submission.Work.Mostow.KMdefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.Margulis.nearId_conj_power_parametric
import Submission.Work.Mostow.HL_of_escapeShort
import Submission.Work.Mostow.no_fixed_of_orderOf_zero
import Submission.Work.Mostow.Margulis.bdFix_size_of_no_fixed_point
import Submission.Work.Mostow.HLlinks
import Submission.Work.Mostow.cuspNoLox

/-!
# KM-G: the short element of a discrete subgroup has an elementary neighbourhood

Let `Γ ≤ PO(n,1)` be discrete, `x ∈ ℍⁿ` and `γ ∈ Γ` of infinite order with `hdist x (γ • x) < ε₂`
for a small `ε₂ > 0`.  Then the set of elements of `Γ` displacing `x` by at most `1` is elementary:
either all of them fix a common boundary point `ξ` and preserve the horospheres at `ξ`
(conclusion (1)), or all of them preserve a common pair `{a,b}` of boundary points
(conclusion (2)).

## Proof

* `Work.Mostow.nearIdAt_of_short` (the pigeonhole on the powers of a short element) gives a power
  `γ ^ m` (`1 ≤ m ≤ M`) which is `NearIdAt x η` with `η := min εM ηL`, where `εM` and `ηL` are the
  Margulis constants of `MargulisCuspProp` and `MargulisLoxProp` for `R = 1`.
* `γ ^ m` has infinite order, hence has no fixed point in `ℍⁿ` (`no_fixed_of_orderOf_zero`), so
  `ClassifyProp` splits `γ ^ m` into the parabolic and the loxodromic case.
* Loxodromic: `MargulisLoxProp` with `R = 1`, applied to the loxodromic element `γ ^ m`, which is
  `NearIdAt x ηL`, gives immediately conclusion (2) with the pair of `γ ^ m`.
* Parabolic: `bdFix_exists_fixed_boundary` supplies the fixed boundary point `ξ` of `γ ^ m`, and
  `MargulisCuspProp` with `R = 1` shows that every `δ` with `hdist x (δ • x) ≤ 1` fixes `ξ`;
  the vanishing of the Busemann shift, `busemann ξ (δ • 0) = 0`, is `Work.Mostow.cuspNoLox`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem shortInfinite (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hM : MargulisCuspProp n) (hL : MargulisLoxProp n) (hC : ClassifyProp n) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
      ∀ (x : E n) (γ : Γ), ¬ IsOfFinOrder γ → hdist x ((γ : PO n 1) • x) < ε₂ →
      (∃ ξ ∈ Sph n, ∀ δ : Γ, hdist x ((δ : PO n 1) • x) ≤ 1 →
          bd (δ : PO n 1) ξ = ξ ∧ busemann ξ ((δ : PO n 1) • (0 : E n)) = 0) ∨
      (∃ a b : E n, a ∈ Sph n ∧ b ∈ Sph n ∧ a ≠ b ∧ ∀ δ : Γ,
          hdist x ((δ : PO n 1) • x) ≤ 1 →
          ((bd (δ : PO n 1) a = a ∧ bd (δ : PO n 1) b = b) ∨
            (bd (δ : PO n 1) a = b ∧ bd (δ : PO n 1) b = a))) := by
  -- the two Margulis constants, for `R = 1`
  obtain ⟨εM, hεMpos, hεM⟩ := hM 1
  obtain ⟨ηL, hηLpos, hηL⟩ := hL 1
  set η : ℝ := min εM ηL with hηdef
  have hηpos : 0 < η := lt_min hεMpos hηLpos
  have hηεM : η ≤ εM := min_le_left _ _
  have hηηL : η ≤ ηL := min_le_right _ _
  -- the pigeonhole: a short element has a near-identity power
  obtain ⟨M, ε₁, hMpos, hε₁pos, hpw⟩ := nearIdAt_of_short n hA hI η hηpos
  refine ⟨ε₁, hε₁pos, ?_⟩
  intro Γ hdisc x γ hnt hshort
  obtain ⟨m, hm1, hmM, hnear⟩ := hpw x (γ : PO n 1) hshort
  -- the short power, as an element of `Γ` and as an element of `PO n 1`
  have hcoe : (((γ ^ m : Γ)) : PO n 1) = (γ : PO n 1) ^ m := Subgroup.coe_pow Γ γ m
  have horder0 : orderOf γ = 0 := orderOf_eq_zero hnt
  have horder_pow : orderOf (γ ^ m : Γ) = 0 := orderOf_pow_eq_zero γ hm1 horder0
  have hnofix_sub : ∀ p : E n, ((γ ^ m : Γ) : PO n 1) • p ≠ p :=
    fun p => no_fixed_of_orderOf_zero n hA hI Γ hdisc (γ ^ m) horder_pow p
  have hnofix : ∀ p : E n, ((γ : PO n 1) ^ m) • p ≠ p := by
    intro p
    rw [← hcoe]
    exact hnofix_sub p
  have hnear' : NearIdAt (((γ ^ m : Γ)) : PO n 1) x η := by rw [hcoe]; exact hnear
  -- classification of the short power
  rcases hC ((γ : PO n 1) ^ m) hnofix with hpar | ⟨a, b, hlox⟩
  · -- parabolic case: everything `1`-short at `x` fixes the cusp point `ξ` of `γ ^ m`
    obtain ⟨ξ, hξS, hξfix⟩ :=
      Work.Mostow.Margulis.bdFix_exists_fixed_boundary n (by omega) hA hI ((γ : PO n 1) ^ m) hnofix
    refine Or.inl ⟨ξ, hξS, ?_⟩
    intro δ hδ
    have hxx : hdist x x ≤ 1 := by
      have h0 : hdist x x = 0 := hdist_self x
      linarith
    have hshortA : hdist x (((γ : PO n 1) ^ m) • x) < εM := by
      have h1 : hdist x (((γ : PO n 1) ^ m) • x) < η := hnear x hxx
      linarith
    have hfixδ : bd (δ : PO n 1) ξ = ξ :=
      hεM Γ hdisc x ξ (γ ^ m) δ (by rw [Subgroup.coe_pow]; exact hpar) hξS
        (by rw [Subgroup.coe_pow]; exact hξfix) hshortA hδ
    have hbus : busemann ξ ((δ : PO n 1) • (0 : E n)) = 0 :=
      cuspNoLox n hA hI Γ hdisc ((γ : PO n 1) ^ m)
        (by rw [← hcoe]; exact (γ ^ m).2) hpar ξ hξS hξfix (δ : PO n 1) δ.2 hfixδ
    exact ⟨hfixδ, hbus⟩
  · -- loxodromic case: `MargulisLoxProp` gives the invariant pair directly
    refine Or.inr ⟨a, b, hlox.1, hlox.2.1, hlox.2.2.1, ?_⟩
    intro δ hδ
    exact hηL Γ hdisc x a b (γ ^ m) δ (by rw [Subgroup.coe_pow]; exact hlox)
      (NearIdAt_mono hnear' hηηL) hδ

end Work.Mostow
