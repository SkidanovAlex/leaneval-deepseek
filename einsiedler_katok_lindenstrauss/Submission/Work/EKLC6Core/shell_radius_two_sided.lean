import Mathlib
import Submission.Work.EKLC6Core.exists_disjoint_three_cover
import Submission.Work.EKLC6Core.sum_sub_le_of_disjoint

namespace Work.EKLC6Core

set_option maxHeartbeats 1000000

/-- **Two-sided shell-radius covering bound.**

For a monotone nonnegative `f : ℝ → ℝ` and `0 < β < γ` there is a radius `s ∈ [β, γ]` at which
the symmetric increments of `f` are controlled by `(16 γ / (γ - β)) δ f (2 γ)` for all `δ ≤ 1`.

The proof is a covering argument.  Suppose every `s ∈ [β, γ]` violates the bound, and let `δ_s` be
a violating radius.  Then the closed intervals `B_s = [s(1-δ_s), s(1+δ_s)]` cover `[β, γ]`
(each `s` lies in `B_s`) and inside `B_s` the increment of `f` exceeds `(8/(γ-β)) f(2γ)` times the
length of `B_s` (because `s ≤ γ` and `B_s` is symmetric about `s`).

The corresponding open intervals contain `[β, γ]`; by compactness finitely many of them do, so a
finite family of open intervals covers `[β, γ]`.  `exists_disjoint_three_cover` extracts a pairwise
disjoint subfamily whose total length is at least a third of `γ - β`.  Over that disjoint family the
increments of `f` sum to at most `f (2γ)` (`sum_sub_le_of_disjoint`), while termwise they dominate
`(8/(γ-β)) f(2γ)` times the total length, hence exceed `(8/3) f(2γ) ≥ f(2γ)`, a contradiction. -/
theorem shell_radius_two_sided (f : ℝ → ℝ) (hf : Monotone f) (hfnn : ∀ t : ℝ, 0 ≤ f t)
    {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ) :
    ∃ s : ℝ, β ≤ s ∧ s ≤ γ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      f (s * (1 + δ)) - f (s * (1 - δ)) ≤ (16 * γ / (γ - β)) * δ * f (2 * γ) := by
  by_contra hcon
  push_neg at hcon
  classical
  have hγβ : 0 < γ - β := by linarith
  let rel : ℝ → ℝ := fun a => if h : a ∈ Set.Icc β γ then (hcon a h.1 h.2).choose else 1 / 2
  have rel_spec : ∀ a, a ∈ Set.Icc β γ → 0 < rel a ∧ rel a ≤ 1 ∧
      (16 * γ / (γ - β)) * rel a * f (2 * γ) <
        f (a * (1 + rel a)) - f (a * (1 - rel a)) := by
    intro a ha
    have hspec := (hcon a ha.1 ha.2).choose_spec
    have heq : rel a = (hcon a ha.1 ha.2).choose := by
      simp only [rel, dif_pos ha]
    rw [heq]
    exact hspec
  -- the open intervals `(a(1-δ), a(1+δ))` over `a ∈ [β,γ]` cover `[β,γ]`
  let U : ↥(Set.Icc β γ) → Set ℝ :=
    fun a => Set.Ioo ((a:ℝ) * (1 - rel (a:ℝ))) ((a:ℝ) * (1 + rel (a:ℝ)))
  have hUopen : ∀ a, IsOpen (U a) := fun a => isOpen_Ioo
  have hcover : Set.Icc β γ ⊆ ⋃ a, U a := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨hpos, hle, _⟩ := rel_spec x hx
    have hx0 : 0 < x := lt_of_lt_of_le hβ hx.1
    simp only [U]
    rw [Set.mem_Ioo]
    constructor <;> nlinarith [hpos, hx0]
  obtain ⟨S, hScover⟩ :=
    IsCompact.elim_finite_subcover isCompact_Icc U hUopen hcover
  let pf : ↥(Set.Icc β γ) → ℝ × ℝ :=
    fun a => ((a:ℝ) * (1 - rel (a:ℝ)), (a:ℝ) * (1 + rel (a:ℝ)))
  let S' : Finset (ℝ × ℝ) := S.image pf
  have hS'cover : Set.Icc β γ ⊆ ⋃ p ∈ S', Set.Ioo p.1 p.2 := by
    intro x hx
    obtain ⟨a, haS, hxa⟩ := Set.mem_iUnion₂.mp (hScover hx)
    refine Set.mem_iUnion₂.mpr ⟨pf a, Finset.mem_image.mpr ⟨a, haS, rfl⟩, ?_⟩
    simpa only [pf, U] using hxa
  have hS'lt : ∀ p ∈ S', p.1 < p.2 := by
    intro p hp
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hpos, hle, _⟩ := rel_spec (a:ℝ) a.2
    have ha0 : 0 < (a:ℝ) := lt_of_lt_of_le hβ a.2.1
    simp only [pf]
    nlinarith [hpos, ha0]
  obtain ⟨T, hTS', hTdisj, hTlen⟩ :=
    exists_disjoint_three_cover S' (le_of_lt hβγ) hS'lt hS'cover
  -- key facts about each member of the disjoint subfamily
  have hkey : ∀ p ∈ T, 0 ≤ p.1 ∧ p.2 ≤ 2 * γ ∧ 0 < p.2 - p.1 ∧
      (8 / (γ - β)) * f (2 * γ) * (p.2 - p.1) < f p.2 - f p.1 := by
    intro p hp
    obtain ⟨a, haS, hpa⟩ := Finset.mem_image.mp (hTS' hp)
    obtain ⟨hpos, hle, hbad⟩ := rel_spec (a:ℝ) a.2
    have ha0 : 0 < (a:ℝ) := lt_of_lt_of_le hβ a.2.1
    have haγ : (a:ℝ) ≤ γ := a.2.2
    have hf2 : 0 ≤ f (2 * γ) := hfnn (2 * γ)
    have hp1 : p.1 = (a:ℝ) * (1 - rel (a:ℝ)) := by rw [← hpa]
    have hp2 : p.2 = (a:ℝ) * (1 + rel (a:ℝ)) := by rw [← hpa]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hp1]; nlinarith [hle, ha0]
    · rw [hp2]; nlinarith [hle, haγ, ha0]
    · rw [hp1, hp2]; nlinarith [hpos, ha0]
    · rw [hp1, hp2]
      rw [show (a:ℝ) * (1 + rel (a:ℝ)) - (a:ℝ) * (1 - rel (a:ℝ))
            = 2 * ((a:ℝ) * rel (a:ℝ)) by ring]
      have hstep : (8 / (γ - β)) * f (2 * γ) * (2 * ((a:ℝ) * rel (a:ℝ))) ≤
          (16 * γ / (γ - β)) * rel (a:ℝ) * f (2 * γ) := by
        rw [show (8 / (γ - β)) * f (2 * γ) * (2 * ((a:ℝ) * rel (a:ℝ)))
              = (16 * (a:ℝ) * rel (a:ℝ) * f (2 * γ)) / (γ - β) by ring,
            show (16 * γ / (γ - β)) * rel (a:ℝ) * f (2 * γ)
              = (16 * γ * rel (a:ℝ) * f (2 * γ)) / (γ - β) by ring]
        rw [div_le_div_iff_of_pos_right hγβ]
        nlinarith [mul_nonneg (le_of_lt hpos) hf2, haγ]
      exact lt_of_le_of_lt hstep hbad
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · exfalso
      rw [h] at hTlen
      simp only [Finset.sum_empty, mul_zero] at hTlen
      linarith
    · exact h
  have hupper : ∑ p ∈ T, (f p.2 - f p.1) ≤ f (2 * γ) := by
    have h1 := sum_sub_le_of_disjoint hf (show (0:ℝ) ≤ 2 * γ by linarith) T
        (fun p hp => ⟨(hkey p hp).1, (hkey p hp).2.1⟩)
        (fun p hp => by have := (hkey p hp).2.2.1; linarith)
        hTdisj
    linarith [hfnn 0]
  have hEach : ∀ p ∈ T, (8 / (γ - β)) * f (2 * γ) * (p.2 - p.1) < f p.2 - f p.1 :=
    fun p hp => (hkey p hp).2.2.2
  have hstrict := Finset.sum_lt_sum_of_nonempty hTne hEach
  have hlen : (γ - β) / 3 ≤ ∑ p ∈ T, (p.2 - p.1) := by linarith [hTlen]
  have hcoef : 0 ≤ (8 / (γ - β)) * f (2 * γ) :=
    mul_nonneg (by positivity) (hfnn (2 * γ))
  have hlow : (8 / (γ - β)) * f (2 * γ) * ((γ - β) / 3) ≤
      ∑ p ∈ T, (8 / (γ - β)) * f (2 * γ) * (p.2 - p.1) := by
    have hfac : ∑ p ∈ T, (8 / (γ - β)) * f (2 * γ) * (p.2 - p.1)
        = (8 / (γ - β)) * f (2 * γ) * ∑ p ∈ T, (p.2 - p.1) := by
      rw [Finset.mul_sum]
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hlen hcoef
  have h8 : (8 / (γ - β)) * f (2 * γ) * ((γ - β) / 3) = (8 / 3) * f (2 * γ) := by
    have hne : γ - β ≠ 0 := ne_of_gt hγβ
    field_simp
  have key1 : (8 / 3) * f (2 * γ) < ∑ p ∈ T, (f p.2 - f p.1) := by
    calc (8 / 3) * f (2 * γ)
        = (8 / (γ - β)) * f (2 * γ) * ((γ - β) / 3) := h8.symm
      _ ≤ ∑ p ∈ T, (8 / (γ - β)) * f (2 * γ) * (p.2 - p.1) := hlow
      _ < ∑ p ∈ T, (f p.2 - f p.1) := hstrict
  have : (8 / 3) * f (2 * γ) < f (2 * γ) := lt_of_lt_of_le key1 hupper
  linarith [this, hfnn (2 * γ)]

end Work.EKLC6Core
