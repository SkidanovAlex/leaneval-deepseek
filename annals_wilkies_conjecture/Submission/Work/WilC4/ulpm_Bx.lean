/-
  WilC4/ulpm_Bx : the crossing family of the ULPM proof.

  `Work.WilC4.ulpm_Bx` takes a `∅`-definable breakpoint family `B₀` off which the doubling ratio
  `RatW Y c · ·` is monotone (three-point condition), and produces a larger `∅`-definable family
  `B ⊇ B₀` with uniformly bounded fibres such that, off `B`, on every interval the ratio either
  avoids `Mid E` entirely or is constantly equal to a single element of `Mid E`.

  The crossing family is `Bx Y E` (`Submission/Work/WilC4/ulpm_BxDefs.lean`): the boundary points
  of the level sets `Sfib Y c m = {x | ∃ w, RatW Y c x w ∧ w = m}`, `m ∈ Mid E`.

  * `Bx` is `∅`-definable (`Bx_definable`, from the parametric boundary lemma
    `paramBnd_definable` and the definability of `Mid E` and of `Sfam Y`);
  * its fibres are uniformly finite (`Bx_fibre_bdd`: the boundary of a definable subset of `ℝ` is
    finite by o-minimality, and `exists_alt_bound` bounds all fibres at once);
  * off `Bx`, every level set is all-or-nothing on every interval
    (`bnd_interval_dichotomy`), so `hmono` confines the attained values in `Mid E` to a single
    one, which is the slot dichotomy proved below.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMB
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.ulpm_BxDefs
import Submission.Work.WilC4.ulpm_BxAux
import Submission.Work.WilC4.bnd_interval_dichotomy
import Submission.Work.WilC4.Mid_definable
import Submission.Work.WilC4.Mid_finite
import Submission.Work.WilC4.Sfam_definable
import Submission.Work.WilC4.Bx_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-- **The slot dichotomy.**  Off `B₀ ∪ Bx Y E` the doubling ratio either avoids `Mid E` on the
whole interval, or is constantly equal to a single element of `Mid E`.

Proof: for every `m ∈ Mid E` the level set `Sfib Y c m` has no boundary point in the interval, so
by `bnd_interval_dichotomy` it either contains the interval or is disjoint from it.  If some `m`
contains the interval, then every point of the interval carries the value `m`; a second value
`w ≠ m` at an interior point would produce the non-monotone triple `(m, w, m)` for `hmono`. -/
theorem slot_dichotomy (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) (E : Set ℝ)
    (hmono : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) →
      ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
        x₁ < x₂ → x₂ < x₃ → RatW Y c x₁ w₁ → RatW Y c x₂ w₂ → RatW Y c x₃ w₃ →
        (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁))
    (c : Fin k → ℝ) (a b : ℝ) (hab : a < b)
    (havb : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀ ∪ Bx Y E) :
    (∀ x ∈ Set.Ioo a b, ∀ w : ℝ, RatW Y c x w → w ∉ Mid E) ∨
    (∃ mid ∈ Mid E, ∀ x ∈ Set.Ioo a b, ∀ w : ℝ, RatW Y c x w → w = mid) := by
  -- no boundary point of a level set with value in `Mid E` lies in the interval
  have hnb : ∀ m ∈ Mid E, ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (Sfib Y c m) x := by
    intro m hm x hx hb
    exact havb x hx (Or.inr ((mem_Bx_iff Y E c x).mpr ⟨m, hm, hb⟩))
  -- dichotomy for every level set
  have hdich : ∀ m ∈ Mid E, Set.Ioo a b ⊆ Sfib Y c m ∨ Set.Ioo a b ⊆ (Sfib Y c m)ᶜ :=
    fun m hm => bnd_interval_dichotomy (fun x hx => hnb m hm x hx)
  by_cases hcase : ∃ m ∈ Mid E, Set.Ioo a b ⊆ Sfib Y c m
  · -- some level set covers the interval: the ratio is constantly equal to that value
    obtain ⟨mid, hmid, hsub⟩ := hcase
    refine Or.inr ⟨mid, hmid, fun x hx w hw => ?_⟩
    by_contra hne
    obtain ⟨x₁, hx₁a, hx₁x⟩ := exists_between hx.1
    obtain ⟨x₂, hxx₂, hx₂b⟩ := exists_between hx.2
    have hx₁ : x₁ ∈ Set.Ioo a b := ⟨hx₁a, lt_trans hx₁x hx.2⟩
    have hx₂ : x₂ ∈ Set.Ioo a b := ⟨lt_trans hx.1 hxx₂, hx₂b⟩
    obtain ⟨w₁, hw₁, hw₁e⟩ := hsub hx₁
    obtain ⟨w₂, hw₂, hw₂e⟩ := hsub hx₂
    have hB₀free : ∀ y ∈ Set.Ioo a b, Fin.cons y c ∉ B₀ :=
      fun y hy hyB => havb y hy (Or.inl hyB)
    rcases hmono c a b hab hB₀free x₁ x x₂ w₁ w w₂ hx₁ hx hx₂ hx₁x hxx₂ hw₁ hw hw₂ with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hw₁e] at h1; rw [hw₂e] at h2; exact hne (le_antisymm h2 h1)
    · rw [hw₂e] at h1; rw [hw₁e] at h2; exact hne (le_antisymm h2 h1)
  · -- no level set covers the interval: no value in `Mid E` is attained
    refine Or.inl fun x hx w hw hwmid => ?_
    rcases hdich w hwmid with hsub | hsub
    · exact absurd ⟨w, hwmid, hsub⟩ hcase
    · exact hsub hx ⟨w, hw, rfl⟩

/-- **Wilkie's conjecture, C4 route: the crossing family.**  Under the monotonicity hypothesis
`hmono` off `B₀`, there is a `∅`-definable breakpoint family `B ⊇ B₀` with uniformly bounded
fibres such that off `B` the doubling ratio either avoids `Mid E` or is constantly equal to a
single element of `Mid E`. -/
theorem ulpm_Bx {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) (N₀ : ℕ)
    (hB₀card : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B₀}.encard ≤ N₀)
    (hmono : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) →
      ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
        x₁ < x₂ → x₂ < x₃ → Work.WilC4.RatW Y c x₁ w₁ → Work.WilC4.RatW Y c x₂ w₂ →
        Work.WilC4.RatW Y c x₃ w₃ →
        (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁))
    (E : Set ℝ) (hEdef : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) (hE : E.Finite) :
    ∃ N : ℕ, ∃ B : Set (Fin (k + 1) → ℝ), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B ∧
      (∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N) ∧ B₀ ⊆ B ∧
      ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
        (∀ x ∈ Set.Ioo a b, ∀ w : ℝ, Work.WilC4.RatW Y c x w → w ∉ Work.WilC4.Mid E) ∨
        (∃ mid ∈ Work.WilC4.Mid E, ∀ x ∈ Set.Ioo a b, ∀ w : ℝ,
          Work.WilC4.RatW Y c x w → w = mid) := by
  -- definability of the ingredients
  have hMid : (∅ : Set ℝ).Definable₁ LRc (Mid E) := Mid_definable E hEdef
  have hSfam : (∅ : Set ℝ).Definable LRc (Sfam Y) := Sfam_definable (k := k) hY
  have hBxdef : (∅ : Set ℝ).Definable LRc (Bx Y E) := Bx_definable (k := k) Y hY E hMid hSfam
  have hMidfin : (Mid E).Finite := Mid_finite E hE
  obtain ⟨N₁, hN₁⟩ := Bx_fibre_bdd (k := k) hOM Y E hSfam hMidfin hBxdef
  refine ⟨N₀ + N₁, B₀ ∪ Bx Y E, hB₀.union hBxdef, ?_, Set.subset_union_left, ?_⟩
  · -- the uniform bound on the fibres of `B₀ ∪ Bx`
    intro c
    have hfib : {x : ℝ | Fin.cons x c ∈ B₀ ∪ Bx Y E} =
        {x : ℝ | Fin.cons x c ∈ B₀} ∪ {x : ℝ | Fin.cons x c ∈ Bx Y E} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [hfib]
    calc (({x : ℝ | Fin.cons x c ∈ B₀} ∪ {x : ℝ | Fin.cons x c ∈ Bx Y E}).encard)
        ≤ ({x : ℝ | Fin.cons x c ∈ B₀}).encard + ({x : ℝ | Fin.cons x c ∈ Bx Y E}).encard :=
          Set.encard_union_le _ _
      _ ≤ ((N₀ : ENat) + (N₁ : ENat)) := add_le_add (hB₀card c) (hN₁ c)
      _ = ((N₀ + N₁ : ℕ) : ENat) := by rw [Nat.cast_add]
  · -- the slot dichotomy
    intro c a b hab havb
    exact slot_dichotomy Y B₀ E hmono c a b hab havb

end Work.WilC4
