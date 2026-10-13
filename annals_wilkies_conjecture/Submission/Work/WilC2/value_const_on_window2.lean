import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.Uniform
import Submission.Work.WilC2.boundary_finite
import Submission.Work.WilC4.sup_exists_dcl
import Submission.Work.WilC2.definable_window_value_class

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG

/-! ## The order-theoretic heart

A subset of a closed interval `[a,b]` of a linear order which is simultaneously "open" and
"closed" inside `[a,b]` (both sides witnessed by `ε`-neighbourhoods, as produced by the local
constancy hypothesis), which is nonempty, and for which both it and its complement in `[a,b]`
admit suprema, must be all of `[a,b]`.

This is the "connectedness of an interval" fact.  It is *not* available from the order axioms
alone (a non-Dedekind-complete linear order has definable-clopen proper subsets of intervals); it
is exactly the point where definable completeness of models of `TR` enters, and it is stated here
with the two suprema as hypotheses so that it can be fed from
`Work.WilC4.sup_exists_dcl`. -/
theorem clopen_Icc_eq {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {S : Set M} {a b : M}
    (hSsub : S ⊆ Set.Icc a b) (hSne : S.Nonempty)
    (hslub : ∃ s : M, IsLUB S s) (htlub : ∃ t : M, IsLUB (Set.Icc a b \ S) t)
    (hSopen : ∀ z ∈ S, ∃ ε : M, 0 < ε ∧ Set.Ioo (z - ε) (z + ε) ∩ Set.Icc a b ⊆ S)
    (hTopen : ∀ z ∈ Set.Icc a b, z ∉ S →
      ∃ ε : M, 0 < ε ∧ Set.Ioo (z - ε) (z + ε) ∩ Set.Icc a b ⊆ Sᶜ) :
    S = Set.Icc a b := by
  obtain ⟨s, hs⟩ := hslub
  obtain ⟨y0, hy0S⟩ := hSne
  -- `s` lies in `[a,b]`
  have ha_s : a ≤ s := le_trans (hSsub hy0S).1 (hs.1 hy0S)
  have hs_b : s ≤ b := hs.2 (fun x hx => (hSsub hx).2)
  have hs_Icc : s ∈ Set.Icc a b := ⟨ha_s, hs_b⟩
  -- `s ∈ S` (else the neighbourhood of `s` given by closedness misses `S`)
  have hs_S : s ∈ S := by
    by_contra hcon
    obtain ⟨ε, hε, hsub⟩ := hTopen s hs_Icc hcon
    have hex : ∃ y ∈ S, s - ε < y := by
      by_contra hc
      push_neg at hc
      have hub : s - ε ∈ upperBounds S := fun x hx => hc x hx
      have := hs.2 hub
      linarith
    obtain ⟨y, hyS, hygt⟩ := hex
    have hyIoo : y ∈ Set.Ioo (s - ε) (s + ε) := ⟨hygt, by linarith [hs.1 hyS]⟩
    exact (hsub ⟨hyIoo, hSsub hyS⟩) hyS
  -- hence `s = b`
  have hs_eq_b : s = b := by
    by_contra hne
    have hlt : s < b := lt_of_le_of_ne hs_b hne
    obtain ⟨ε, hε, hsub⟩ := hSopen s hs_S
    set z : M := min (s + ε / 2) b with hzdef
    have hsz : s < z := by
      rw [hzdef]; exact lt_min (by linarith) hlt
    have hz_lt : z < s + ε := by
      rw [hzdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hzIoo : z ∈ Set.Ioo (s - ε) (s + ε) := ⟨by linarith, hz_lt⟩
    have hzIcc : z ∈ Set.Icc a b := ⟨by linarith, by rw [hzdef]; exact min_le_right _ _⟩
    exact absurd (hs.1 (hsub ⟨hzIoo, hzIcc⟩)) (not_le.mpr hsz)
  have hb_S : b ∈ S := hs_eq_b ▸ hs_S
  -- the complement in `[a,b]` is empty: the same argument applied to it
  by_contra hST
  have hTne : (Set.Icc a b \ S).Nonempty := by
    by_contra hh
    rw [Set.not_nonempty_iff_eq_empty] at hh
    refine hST (Set.Subset.antisymm hSsub ?_)
    intro x hx
    by_contra hxS
    have : x ∈ Set.Icc a b \ S := ⟨hx, hxS⟩
    rw [hh] at this
    exact this
  obtain ⟨t, ht⟩ := htlub
  obtain ⟨y1, hy1T⟩ := hTne
  have ha_t : a ≤ t := le_trans hy1T.1.1 (ht.1 hy1T)
  have ht_b : t ≤ b := ht.2 (fun x hx => hx.1.2)
  have ht_Icc : t ∈ Set.Icc a b := ⟨ha_t, ht_b⟩
  have ht_T : t ∈ Set.Icc a b \ S := by
    by_contra hcon
    have ht_S : t ∈ S := by
      by_contra htS
      exact hcon ⟨ht_Icc, htS⟩
    obtain ⟨ε, hε, hsub⟩ := hSopen t ht_S
    have hex : ∃ y ∈ Set.Icc a b \ S, t - ε < y := by
      by_contra hc
      push_neg at hc
      have hub : t - ε ∈ upperBounds (Set.Icc a b \ S) := fun x hx => hc x hx
      have := ht.2 hub
      linarith
    obtain ⟨y, hyT, hygt⟩ := hex
    have hyIoo : y ∈ Set.Ioo (t - ε) (t + ε) := ⟨hygt, by linarith [ht.1 hyT]⟩
    exact hyT.2 (hsub ⟨hyIoo, hyT.1⟩)
  have ht_eq_b : t = b := by
    by_contra hne
    have hlt : t < b := lt_of_le_of_ne ht_b hne
    obtain ⟨ε, hε, hsub⟩ := hTopen t ht_Icc ht_T.2
    set z : M := min (t + ε / 2) b with hzdef
    have htz : t < z := by
      rw [hzdef]; exact lt_min (by linarith) hlt
    have hz_lt : z < t + ε := by
      rw [hzdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hzIoo : z ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, hz_lt⟩
    have hzIcc : z ∈ Set.Icc a b := ⟨by linarith, by rw [hzdef]; exact min_le_right _ _⟩
    exact absurd (ht.1 ⟨hzIcc, hsub ⟨hzIoo, hzIcc⟩⟩) (not_le.mpr htz)
  exact (ht_eq_b ▸ ht_T.2) hb_S

/-! ## The value class of `y` in the window spanned by `y` and `y'` -/

/-- Points `z` of the interval `[min y y', max y y']` such that `P y ·` and `P z ·` share a
witness — i.e. (using uniqueness on `H`) the points of the window on which the value of the fibre
of `P` agrees with that at `y`. -/
abbrev winClass {M : Type} [LinearOrder M] (P : M → M → Prop) (y y' : M) : Set M :=
  {z : M | z ∈ Set.Icc (min y y') (max y y') ∧ ∃ w : M, P y w ∧ P z w}

/-- A `T`-definable relation that is "locally constant" on a `T`-definable set `H`, with nonempty
fibres on `H`, is constant on the order-convex pieces of `H`: if the whole interval between
`y, y' ∈ H` lies in `H`, and the fibres `P y ·`, `P y' ·` are singletons with values `x`, `x'`,
then `x = x'`.

(The fibre over `y'` is nonempty by `hne`, so `hx'` exhibits its value.  Note that "connectedness"
must be obtained from definable completeness: the schema "a nonempty bounded definable set has a
supremum" is a first-order sentence scheme, true in `ℝ`, hence holds in every model of
`TR`; use it to rule out a definable clopen subset of an interval.  The companion lemma
`Work.WilC2.boundary_finite` gives the finiteness of the boundary set.) -/
theorem value_const_on_window2
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] {T : Set M} (hT : Dcl T ⊆ T)
    {H : Set M} (hH : T.Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ H})
    {P : M → M → Prop} (hP : T.Definable WilkiesDesign.CG.LRc {v : Fin 2 → M | P (v 0) (v 1)})
    (hne : ∀ y ∈ H, ∃ x : M, P y x)
    (huniq : ∀ y ∈ H, ∀ x x' : M, P y x → P y x' → x = x')
    (hloc : ∀ y ∈ H, ∃ ε : M, 0 < ε ∧ ∀ z ∈ Set.Ioo (y - ε) (y + ε), z ∈ H → ∀ x : M, P y x → P z x)
    {y y' : M} (hy : y ∈ H) (hy' : y' ∈ H) (hr : Set.Icc (min y y') (max y y') ⊆ H)
    {x x' : M} (hx : P y x) (hx' : P y' x') : x = x' := by
  classical
  have hM : M ⊨ WilkiesDesign.CG.TR := inferInstance
  -- definability of the interval and of the value class (delegated, mechanical)
  obtain ⟨hIcc, hSdefn⟩ := definable_window_value_class hM hP y y'
  -- definability of the complement of the class inside the interval
  have hTdefn : (Set.univ : Set M).Definable₁ WilkiesDesign.CG.LRc
      (Set.Icc (min y y') (max y y') \ winClass P y y') := by
    have h := hIcc.inter hSdefn.compl
    change (Set.univ : Set M).Definable WilkiesDesign.CG.LRc
      {v : Fin 1 → M | v 0 ∈ Set.Icc (min y y') (max y y') \ winClass P y y'}
    exact h
  -- structural facts
  have hSsub : winClass P y y' ⊆ Set.Icc (min y y') (max y y') := fun z hz => hz.1
  have hSne : (winClass P y y').Nonempty :=
    ⟨y, ⟨⟨min_le_left y y', le_max_left y y'⟩, x, hx, hx⟩⟩
  have hslub : ∃ s : M, IsLUB (winClass P y y') s := by
    obtain ⟨s, hs, _⟩ :=
      Work.WilC4.sup_exists_dcl hM hSdefn hSne ⟨max y y', fun z hz => hz.1.2⟩
    exact ⟨s, hs⟩
  -- openness of the class (local constancy at points of the class)
  have hSopen : ∀ z ∈ winClass P y y', ∃ ε : M, 0 < ε ∧
      Set.Ioo (z - ε) (z + ε) ∩ Set.Icc (min y y') (max y y') ⊆ winClass P y y' := by
    intro z hz
    obtain ⟨hzIcc, w0, hyw0, hzw0⟩ := hz
    obtain ⟨ε, hε, hloc_z⟩ := hloc z (hr hzIcc)
    exact ⟨ε, hε, fun ζ hζ => ⟨hζ.2, w0, hyw0, hloc_z ζ hζ.1 (hr hζ.2) w0 hzw0⟩⟩
  -- openness of the complement (local constancy at points outside the class)
  have hTopen : ∀ z ∈ Set.Icc (min y y') (max y y'), z ∉ winClass P y y' → ∃ ε : M, 0 < ε ∧
      Set.Ioo (z - ε) (z + ε) ∩ Set.Icc (min y y') (max y y') ⊆ (winClass P y y')ᶜ := by
    intro z hzIcc hzS
    obtain ⟨w0, hzw0⟩ := hne z (hr hzIcc)
    obtain ⟨ε, hε, hloc_z⟩ := hloc z (hr hzIcc)
    exact ⟨ε, hε, fun ζ hζ hζS => by
      obtain ⟨-, w', hyw', hζw'⟩ := hζS
      have hζw0 : P ζ w0 := hloc_z ζ hζ.1 (hr hζ.2) w0 hzw0
      have : w0 = w' := huniq ζ (hr hζ.2) w0 w' hζw0 hζw'
      exact hzS ⟨hzIcc, w0, this.symm ▸ hyw', hzw0⟩⟩
  -- the class fills the whole window
  have hseq : winClass P y y' = Set.Icc (min y y') (max y y') := by
    by_cases hTne : (Set.Icc (min y y') (max y y') \ winClass P y y').Nonempty
    · obtain ⟨t, ht, _⟩ :=
        Work.WilC4.sup_exists_dcl hM hTdefn hTne ⟨max y y', fun z hz => hz.1.2⟩
      exact clopen_Icc_eq hSsub hSne hslub ⟨t, ht⟩ hSopen hTopen
    · have hsub : Set.Icc (min y y') (max y y') ⊆ winClass P y y' := by
        intro z hz
        by_contra hzS
        exact hTne ⟨z, hz, hzS⟩
      exact Set.Subset.antisymm hSsub hsub
  -- in particular `y'` lies in the class, so the two fibres share a witness
  have hy'S : y' ∈ winClass P y y' := by
    rw [hseq]
    exact ⟨min_le_right y y', le_max_right y y'⟩
  obtain ⟨-, w, hyw, hy'w⟩ := hy'S
  rw [huniq y hy x w hx hyw, huniq y' hy' x' w hx' hy'w]

end Work.WilC2
