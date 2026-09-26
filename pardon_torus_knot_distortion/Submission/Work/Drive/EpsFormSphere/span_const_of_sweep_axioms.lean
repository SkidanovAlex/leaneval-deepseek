import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# Constancy of the winding span along a sweep with finitely many exceptional parameters

This file proves `Work.Drive.EpsFormSphere.span_const_of_sweep_axioms`, the purely
combinatorial/one-dimensional bookkeeping that turns the local data of a sideways sweep
(`SideSweepData` in `Submission/Work/Drive/EpsFormSphere/Sideways.lean`) into the constancy of
the winding span between the two ends of the sweep.

The region `X lam` of the surface is assumed to vary monotonically, to have a *constant* winding
span on every interval which contains no exceptional parameter (`hreg`), to change the
`ℚ`-dimension of its winding span by at most one across a single exceptional parameter
(`hjump`), and to have winding span `⊥` or `⊤` at every regular parameter (`hdich`, the trace
at a regular level being a finite union of inessential curves).  Since `⊥` and `⊤` are the only
subspaces of `ℚ²` which can appear at the intermediate parameters, and `finrank ⊥ = 0` while
`finrank ⊤ = 2`, the `≤ 1` bound at each exceptional parameter forces all the intermediate
spans to be equal; hence the spans at the two ends agree.
-/

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion

/-- A submodule of `ℚ²` which is either `⊥` or `⊤` is determined by its `ℚ`-dimension.  In
particular, if the dimensions of two such submodules differ by at most one, they are equal:
the only possible dimensions are `0` and `2`. -/
private lemma dichotomy_finrank_eq (A B : Submodule ℚ (ℚ × ℚ))
    (hA : A = ⊥ ∨ A = ⊤) (hB : B = ⊥ ∨ B = ⊤)
    (h1 : Module.finrank ℚ ↥A ≤ Module.finrank ℚ ↥B + 1)
    (h2 : Module.finrank ℚ ↥B ≤ Module.finrank ℚ ↥A + 1) : A = B := by
  have hbot : Module.finrank ℚ ↥(⊥ : Submodule ℚ (ℚ × ℚ)) = 0 := finrank_bot ℚ _
  have htop : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
    rw [finrank_top, Module.finrank_prod, Module.finrank_self]
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · rfl
  · rw [htop, hbot] at h2
    exact absurd h2 (by omega)
  · rw [htop, hbot] at h1
    exact absurd h1 (by omega)
  · rfl

/-- **The bookkeeping lemma.**  Let `W : ℝ → Submodule ℚ (ℚ × ℚ)` be a family of subspaces
indexed by an interval `[a, b]`, let `T` be a finite set of "exceptional" parameters inside
`(a, b)`, and assume that

* `hreg`: `W` is constant on every subinterval of `[a, b]` containing no point of `T`;
* `hjump`: across a single point `lam ∈ T` the dimensions of `W` change by at most one;
* `hdich`: at every parameter of `[a, b] \ T`, `W` is either `⊥` or `⊤`.

Then `W a = W b`.

The proof is by induction on `T`, peeling off the largest exceptional parameter `e`: choose a
parameter `w` between the next exceptional parameter and `e`; the jump estimate at `e` together
with the dichotomy at `w` and at `b` gives `W w = W b`, and the induction hypothesis applied to
the remaining exceptional parameters on the interval `[a, w]` gives `W a = W w`. -/
private lemma span_eq_of_finset_sweep (W : ℝ → Submodule ℚ (ℚ × ℚ)) :
    ∀ (T : Finset ℝ) (a b : ℝ), a < b →
      (∀ t ∈ T, a < t ∧ t < b) →
      (∀ μ ν, a ≤ μ → μ ≤ ν → ν ≤ b → (∀ t ∈ T, t < μ ∨ ν < t) → W μ = W ν) →
      (∀ lam ∈ T, ∀ μ ν, a ≤ μ → μ < lam → lam < ν → ν ≤ b →
        (∀ t ∈ T, t < μ ∨ t = lam ∨ ν < t) →
        Module.finrank ℚ ↥(W μ) ≤ Module.finrank ℚ ↥(W ν) + 1 ∧
        Module.finrank ℚ ↥(W ν) ≤ Module.finrank ℚ ↥(W μ) + 1) →
      (∀ lam, a ≤ lam → lam ≤ b → lam ∉ T → W lam = ⊥ ∨ W lam = ⊤) →
      W a = W b := by
  intro T
  induction T using Finset.induction_on_max with
  | empty =>
    intro a b hab hT hreg hjump hdich
    exact hreg a b le_rfl hab.le le_rfl (fun t ht => by simp at ht)
  | insert e s hlt ih =>
    intro a b hab hT hreg hjump hdich
    by_cases hs : s = ∅
    · -- the only exceptional parameter is `e`: jump directly from `a` to `b`
      subst hs
      have heT : e ∈ insert e (∅ : Finset ℝ) := Finset.mem_insert_self e ∅
      have hae : a < e := (hT e heT).1
      have heb : e < b := (hT e heT).2
      have hmem : ∀ t, t ∈ insert e (∅ : Finset ℝ) ↔ t = e := fun t => by simp
      have hbnd := hjump e heT a b le_rfl hae heb le_rfl
        (fun t ht => Or.inr (Or.inl ((hmem t).mp ht)))
      have ha_d := hdich a le_rfl hab.le (fun h => by
        have h' : a = e := (hmem a).mp h
        linarith)
      have hb_d := hdich b hab.le le_rfl (fun h => by
        have h' : b = e := (hmem b).mp h
        linarith)
      exact dichotomy_finrank_eq _ _ ha_d hb_d hbnd.1 hbnd.2
    · -- `e` is the largest exceptional parameter; step over it to a parameter `w` between the
      -- second largest exceptional parameter `m` and `e`, then induct on the remaining ones
      obtain ⟨m, hms, hmle⟩ : ∃ m ∈ s, ∀ t ∈ s, t ≤ m :=
        ⟨s.max' (Finset.nonempty_iff_ne_empty.mpr hs), Finset.max'_mem s _,
          fun t ht => Finset.le_max' s t ht⟩
      have heb : e < b := (hT e (Finset.mem_insert_self e s)).2
      have hme : m < e := hlt m hms
      have hame : a < m := (hT m (Finset.mem_insert_of_mem hms)).1
      have hmw : m < (m + e) / 2 := by linarith
      have hwe : (m + e) / 2 < e := by linarith
      have haw : a < (m + e) / 2 := lt_trans hame hmw
      have hws : ∀ t ∈ s, t < (m + e) / 2 := fun t ht => lt_of_le_of_lt (hmle t ht) hmw
      have hwT : (m + e) / 2 ∉ insert e s := by
        intro h
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · exact absurd h (ne_of_lt hwe)
        · exact absurd (hws ((m + e) / 2) h) (lt_irrefl _)
      have hbT : b ∉ insert e s := by
        intro h
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · linarith
        · exact absurd (hT b (Finset.mem_insert_of_mem h)).2 (lt_irrefl b)
      have hcond : ∀ t ∈ insert e s, t < (m + e) / 2 ∨ t = e ∨ b < t := by
        intro t ht
        rw [Finset.mem_insert] at ht
        rcases ht with rfl | ht
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (hws t ht)
      have hjb := hjump e (Finset.mem_insert_self e s) ((m + e) / 2) b
        (le_of_lt haw) hwe heb le_rfl hcond
      have hdw := hdich ((m + e) / 2) (le_of_lt haw) (le_of_lt (lt_trans hwe heb)) hwT
      have hdb := hdich b hab.le le_rfl hbT
      have hwb : W ((m + e) / 2) = W b := dichotomy_finrank_eq _ _ hdw hdb hjb.1 hjb.2
      have ihs : W a = W ((m + e) / 2) := ih a ((m + e) / 2) haw
        (fun t ht => ⟨(hT t (Finset.mem_insert_of_mem ht)).1, hws t ht⟩)
        (fun μ ν haμ hμν hνw hc =>
          hreg μ ν haμ hμν (le_trans hνw (le_of_lt (lt_trans hwe heb))) (fun t ht => by
            rw [Finset.mem_insert] at ht
            rcases ht with rfl | ht
            · exact Or.inr (lt_of_le_of_lt hνw hwe)
            · exact hc t ht))
        (fun lam hlam μ ν haμ hμl hlν hνw hc =>
          hjump lam (Finset.mem_insert_of_mem hlam) μ ν haμ hμl hlν
            (le_trans hνw (le_of_lt (lt_trans hwe heb))) (fun t ht => by
              rw [Finset.mem_insert] at ht
              rcases ht with rfl | ht
              · exact Or.inr (Or.inr (lt_of_le_of_lt hνw hwe))
              · exact hc t ht))
        (fun lam halam hlamw hlamT => hdich lam halam
          (le_trans hlamw (le_of_lt (lt_trans hwe heb))) (fun h => by
            rw [Finset.mem_insert] at h
            rcases h with h | h
            · linarith
            · exact hlamT h))
      exact ihs.trans hwb

theorem span_const_of_sweep_axioms (P : Work.CoreTopology.ParamTorus)
    (X : ℝ → Set LeanEval.KnotTheory.PardonDistortion.R3)
    (lam0 lam1 : ℝ) (exc : Finset ℝ) (hl : lam0 < lam1)
    (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1)
    (hmono : ∀ μ ν : ℝ, μ ≤ ν → X ν ⊆ X μ)
    (hreg : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 →
      (∀ t ∈ exc, t < μ ∨ ν < t) →
      Work.SurgeryInvariance.WindingSpan P (X μ) =
        Work.SurgeryInvariance.WindingSpan P (X ν))
    (hjump : ∀ lam ∈ exc, ∀ μ ν : ℝ, lam0 ≤ μ → μ < lam → lam < ν → ν ≤ lam1 →
      (∀ t ∈ exc, t < μ ∨ t = lam ∨ ν < t) →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X μ)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X ν)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X ν)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X μ)) + 1)
    (hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      Work.SurgeryInvariance.WindingSpan P (X lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan P (X lam) = ⊤) :
    Work.SurgeryInvariance.WindingSpan P (X lam0) =
      Work.SurgeryInvariance.WindingSpan P (X lam1) := by
  -- the monotonicity hypothesis is not needed by the bookkeeping argument below
  have _hmono := hmono
  exact span_eq_of_finset_sweep (fun lam => Work.SurgeryInvariance.WindingSpan P (X lam))
    exc lam0 lam1 hl hexc hreg hjump
    (fun lam hl0 hl1 hnot => hdich lam hl0 hl1 (fun t ht heq => hnot (heq ▸ ht)))

end Work.Drive.EpsFormSphere
