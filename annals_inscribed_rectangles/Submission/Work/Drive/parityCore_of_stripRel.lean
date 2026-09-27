import Mathlib
import Submission.Work.Drive.OrderRelation
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.Interfaces

namespace Work.Drive

/-! # Guidance (parent agent `orderSplit_chains`) — parityCore_of_stripRel

`Work.Drive.StripRel γ Rel` (`Submission/Work/Drive/OrderRelation.lean`) collects the four properties of
the pairwise order `Rel = ≺` on the rotations of the configuration Möbius strip `M` of `γ`:
antisymmetry on pairs of disjoint strips (`v - u ∈ Zc γ`), invariance under simultaneous rotation,
transitivity, and openness.  This statement derives the `ZMod 2`-valued order function `ParityCore γ`
from them, which is the whole content of the "order split" once the pairwise relation is available.

Take `b u := if Rel 0 u then 1 else 0` on `Zc γ`.  Then:

* *Antisymmetry.*  For `u ∈ Zc γ`, clause 1 at the pair `(0, u)` gives `Rel 0 u ↔ ¬ Rel u 0`, and clause
  2 with `w = -u` gives `Rel u 0 ↔ Rel (u + (-u)) (0 + (-u)) = Rel 0 (-u)`.  Hence
  `Rel 0 u ↔ ¬ Rel 0 (-u)`, i.e. `b u + b (-u) = 1`.  (This is where the relation formulation pays off:
  at `u = 1/2` it reads `b u + b u = 1`, which simply forces `1/2 ∉ Zc γ`, i.e. the inscribed square —
  see `one_half_mem_GoodC_of_stripRel`.  No separate treatment of `u = 1/2` is needed.)
* *Transitivity.*  If `a, c, a+c ∈ Zc γ` and `b a = b c = 1`, then `Rel 0 a` and `Rel 0 c`; clause 2 with
  `w = c` turns `Rel 0 a` into `Rel c (a+c)`, and clause 3 applied to `(0, c, a+c)` (all three differences
  lie in `Zc γ`) gives `Rel 0 (a+c)`, i.e. `b (a+c) = 1`.
* *Continuity.*  `b` is locally constant on the subtype `Zc γ`: if `Rel 0 u`, clause 4 at `(0, u)` gives an
  open `U ∋ 0, u` on which `Rel` is constant, and for any `v ∈ U ∩ Zc γ` clause 4 at `(0, v)` gives
  `Rel 0 v`, so `b v = 1`; if instead `¬ Rel 0 u`, use clause 1 to get `Rel u 0`, apply clause 4 at
  `(u, 0)`, and for `v ∈ U ∩ Zc γ` apply it at `(v, 0)` to get `Rel v 0`, hence `¬ Rel 0 v` and
  `b v = 0`.  Conclude with `continuous_iff_continuousAt` (or local constancy on the subtype).

Note that `IsOpen (Zc γ)` is *not* needed: continuity of `b` is continuity on the subtype `Zc γ`.-/
open Manifold in
open scoped Manifold ContDiff in
/-- The `ZMod 2`-valued "side" function `b u = 1` iff `M ≺ u·M`, attached to a pairwise relation `Rel`. -/
private noncomputable def sideFun (Rel : UnitAddCircle → UnitAddCircle → Prop) (γ : Circle → ℝ × ℝ) :
    Zc γ → ZMod 2 := by
  classical
  exact fun x => if Rel 0 x.1 then 1 else 0

private lemma sideFun_one {γ : Circle → ℝ × ℝ} {Rel : UnitAddCircle → UnitAddCircle → Prop}
    (x : Zc γ) : sideFun Rel γ x = (1 : ZMod 2) ↔ Rel 0 x.1 := by
  classical
  simp only [sideFun]
  by_cases h : Rel 0 x.1
  · simp [h]
  · simp [h]

private lemma sideFun_zero {γ : Circle → ℝ × ℝ} {Rel : UnitAddCircle → UnitAddCircle → Prop}
    (x : Zc γ) : sideFun Rel γ x = (0 : ZMod 2) ↔ ¬ Rel 0 x.1 := by
  classical
  simp only [sideFun]
  by_cases h : Rel 0 x.1
  · simp [h]
  · simp [h]

/-- The pairwise order relation on rotations of the configuration strip produces the `ZMod 2`-valued
order function of the order split. -/
theorem parityCore_of_stripRel {γ : Circle → ℝ × ℝ}
    {Rel : UnitAddCircle → UnitAddCircle → Prop} (h : Work.Drive.StripRel γ Rel) :
    Work.Drive.ParityCore γ := by
  classical
  obtain ⟨hanti, hrot, htrans, hopen⟩ := h
  refine ⟨sideFun Rel γ, ?hcont, ?hsym, ?htrans⟩
  · -- `b` is locally constant on `Zc γ`, hence continuous.
    have hloc : IsLocallyConstant (sideFun Rel γ) := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hru : Rel 0 x.1
      · obtain ⟨U, V, hUopen, hVopen, h0U, hxV, hUVrel⟩ := hopen 0 x.1 (by simpa using x.2) hru
        refine ⟨Subtype.val ⁻¹' V, hVopen.preimage continuous_subtype_val, hxV, ?_⟩
        intro y hy
        have hyr : Rel 0 y.1 := hUVrel 0 h0U y.1 hy (by simpa using y.2)
        rw [sideFun_one y |>.mpr hyr, sideFun_one x |>.mpr hru]
      · have hru' : Rel x.1 0 := by
          by_contra hc
          exact hru ((hanti 0 x.1 (by simpa using x.2)).mpr hc)
        obtain ⟨U, V, hUopen, hVopen, hxU, h0V, hUVrel⟩ := hopen x.1 0 (by simpa using neg_mem_Zc x.2) hru'
        refine ⟨Subtype.val ⁻¹' U, hUopen.preimage continuous_subtype_val, hxU, ?_⟩
        intro y hy
        have hyr : Rel y.1 0 := hUVrel y.1 hy 0 h0V (by simpa using neg_mem_Zc y.2)
        have h1 : ¬ Rel 0 y.1 := fun hh => (hanti 0 y.1 (by simpa using y.2)).mp hh hyr
        rw [sideFun_zero y |>.mpr h1, sideFun_zero x |>.mpr hru]
    exact IsLocallyConstant.continuous hloc
  · -- Antisymmetry: `Rel 0 u ↔ ¬ Rel 0 (-u)`.
    intro u hu
    have h1 : Rel 0 u ↔ ¬ Rel u 0 := hanti 0 u (by simpa using hu)
    have h2 : Rel u 0 ↔ Rel 0 (-u) := by
      have hh := hrot u 0 (-u)
      simpa using hh
    have h3 : Rel 0 u ↔ ¬ Rel 0 (-u) := by rw [h1, h2]
    by_cases hru : Rel 0 u
    · have hnu : ¬ Rel 0 (-u) := h3.mp hru
      have hA : sideFun Rel γ ⟨u, hu⟩ = 1 := (sideFun_one ⟨u, hu⟩).mpr hru
      have hB : sideFun Rel γ ⟨-u, neg_mem_Zc hu⟩ = 0 := (sideFun_zero ⟨-u, neg_mem_Zc hu⟩).mpr hnu
      rw [hA, hB]; simp
    · have hnu : Rel 0 (-u) := by
        by_contra hc
        exact hru (h3.mpr hc)
      have hA : sideFun Rel γ ⟨u, hu⟩ = 0 := (sideFun_zero ⟨u, hu⟩).mpr hru
      have hB : sideFun Rel γ ⟨-u, neg_mem_Zc hu⟩ = 1 := (sideFun_one ⟨-u, neg_mem_Zc hu⟩).mpr hnu
      rw [hA, hB]; simp
  · -- Transitivity, using rotation invariance and clause 3 at `(0, c, a+c)`.
    intro a ha c hc hba hbc hac
    have hra : Rel 0 a := (sideFun_one ⟨a, ha⟩).mp hba
    have hrc : Rel 0 c := (sideFun_one ⟨c, hc⟩).mp hbc
    have hr : Rel c (a + c) := by
      have hh := hrot 0 a c
      rw [zero_add] at hh
      exact hh.mp hra
    have hrr : Rel 0 (a + c) :=
      htrans 0 c (a + c) (by simpa using hc) (by simpa using ha) (by simpa using hac) hrc hr
    exact (sideFun_one ⟨a + c, hac⟩).mpr hrr

end Work.Drive
