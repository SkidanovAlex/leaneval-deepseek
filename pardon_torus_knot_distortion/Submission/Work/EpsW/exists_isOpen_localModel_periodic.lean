import Mathlib
import ChallengeDeps
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.LocallyArcInPlane
import Submission.Work.Smooth.SphereJordan.localArcOfSphere
import Submission.Work.Smooth.JordanSeparationCutting.isLocallyArc_of_periodic_injOn

/-!
# The local model of a periodic injective curve in `ℝ³`

Let `γ : ℝ → ℝ³` be continuous, `2π`-periodic and injective on the fundamental period
`[0, 2π)`.  Then `γ` presents its trace `Set.range γ` as a simple closed curve, and the image of a
parameter interval `(t₀ - δ, t₀ + δ)` is exactly the trace of an *open* set of the ambient space:
for every `t₀` and every `δ > 0` there is an open `O ∋ γ t₀` with

`O ∩ Set.range γ = γ '' (t₀ - δ, t₀ + δ)`.

The content is that the image of the parameter interval is open in the subspace `Set.range γ`.
Equivalently, its complement `Set.range γ \ γ '' (t₀ - δ, t₀ + δ)` — the "rest of the curve" — is
closed.  The proof is short once the period lattice is understood:

* `eq_mod_period_of_eq_periodic` : two parameters with the same image differ by a multiple of `2π`;
* hence the set of parameters mapping into `γ '' P` is `⋃ k : ℤ, (P - k·2π)`, a union of translates
  of the *open* interval `P`, so it is open;
* reducing parameters into the compact interval `[0, 2π]` shows that the rest of the curve is the
  continuous image of a compact set, hence closed.
-/

namespace Work.EpsW

open Set

/-! ## The period lattice -/

/-- Reduction of a real number modulo `2π` into the fundamental interval `[0, 2π)` by an integer
multiple of the period. -/
lemma exists_int_sub_period_mem_Ico (x : ℝ) :
    ∃ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∈ Set.Ico 0 (2 * Real.pi) := by
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  refine ⟨⌊x / (2 * Real.pi)⌋, ?_⟩
  have h1 : ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ x / (2 * Real.pi) := Int.floor_le _
  have h2 : x / (2 * Real.pi) < ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have h3 : ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ x := by
    have hh := mul_le_mul_of_nonneg_right h1 (le_of_lt hp)
    rwa [div_mul_cancel₀ _ (ne_of_gt hp)] at hh
  have h4 : x < ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    have hh := mul_lt_mul_of_pos_right h2 hp
    have h2' : x / (2 * Real.pi) * (2 * Real.pi) = x := div_mul_cancel₀ _ (ne_of_gt hp)
    have h3' : (((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi)
        = ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + 2 * Real.pi := by ring
    linarith [hh, h2', h3']
  rw [Set.mem_Ico]
  exact ⟨by linarith, by linarith⟩

/-- **Two parameters with the same image differ by a period.**  For a `2π`-periodic map which is
injective on the fundamental period `[0, 2π)`, a coincidence `f a = f b` forces `b - a` to be an
integer multiple of `2π`. -/
lemma eq_mod_period_of_eq_periodic {X : Type*} {f : ℝ → X}
    (hper : Function.Periodic f (2 * Real.pi))
    (hinj : Set.InjOn f (Set.Ico 0 (2 * Real.pi))) {a b : ℝ} (h : f a = f b) :
    ∃ k : ℤ, b - a = (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨ka, ha⟩ := exists_int_sub_period_mem_Ico a
  obtain ⟨kb, hb⟩ := exists_int_sub_period_mem_Ico b
  have e1 : f (a - (ka : ℝ) * (2 * Real.pi)) = f a := by
    have hh := (hper.int_mul ka) (a - (ka : ℝ) * (2 * Real.pi))
    rw [show a - (ka : ℝ) * (2 * Real.pi) + (ka : ℝ) * (2 * Real.pi) = a by ring] at hh
    exact hh.symm
  have e2 : f (b - (kb : ℝ) * (2 * Real.pi)) = f b := by
    have hh := (hper.int_mul kb) (b - (kb : ℝ) * (2 * Real.pi))
    rw [show b - (kb : ℝ) * (2 * Real.pi) + (kb : ℝ) * (2 * Real.pi) = b by ring] at hh
    exact hh.symm
  have h1 : a - (ka : ℝ) * (2 * Real.pi) = b - (kb : ℝ) * (2 * Real.pi) :=
    hinj ha hb (by rw [e1, e2, h])
  refine ⟨kb - ka, ?_⟩
  push_cast
  linarith

/-- **The parameters mapping into the image of a set of parameters.**  For a `2π`-periodic map
which is injective on the fundamental period, `f s` lies in the image of `P` exactly when some
translate of `s` by an integer multiple of `2π` lies in `P`. -/
lemma mem_image_iff_exists_period_sub_mem {X : Type*} {f : ℝ → X}
    (hper : Function.Periodic f (2 * Real.pi))
    (hinj : Set.InjOn f (Set.Ico 0 (2 * Real.pi))) {P : Set ℝ} {s : ℝ} :
    f s ∈ f '' P ↔ ∃ k : ℤ, s - (k : ℝ) * (2 * Real.pi) ∈ P := by
  constructor
  · rintro ⟨t, htP, hts⟩
    obtain ⟨k, hk⟩ := eq_mod_period_of_eq_periodic hper hinj hts
    exact ⟨k, by rwa [show s - (k : ℝ) * (2 * Real.pi) = t by linarith]⟩
  · rintro ⟨k, hk⟩
    refine ⟨s - (k : ℝ) * (2 * Real.pi), hk, ?_⟩
    have hh := (hper.int_mul k) (s - (k : ℝ) * (2 * Real.pi))
    rw [show s - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = s by ring] at hh
    exact hh.symm

/-! ## The local model -/

open LeanEval.KnotTheory.PardonDistortion in
/-- **The local model of a periodic injective curve.**  If `γ : ℝ → ℝ³` is continuous, `2π`-periodic and injective on `[0, 2π)`, then for every parameter `t₀` and every `δ > 0` there is an open set `O ∋ γ t₀` whose trace on `Set.range γ` is exactly the image of the parameter interval `(t₀ - δ, t₀ + δ)`. -/
theorem exists_isOpen_localModel_periodic {γ : ℝ → R3}
    (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (t₀ δ : ℝ) (hδ : 0 < δ) :
    ∃ O : Set R3, IsOpen O ∧ γ t₀ ∈ O ∧
      O ∩ Set.range γ = γ '' Set.Ioo (t₀ - δ) (t₀ + δ) := by
  classical
  set P : Set ℝ := Set.Ioo (t₀ - δ) (t₀ + δ) with hP
  set A : Set R3 := γ '' P with hA
  -- The parameters mapping into `A` form an open set: it is a union of translates of the open
  -- interval `P`.
  have hTopen : IsOpen {s : ℝ | γ s ∈ A} := by
    have heq : {s : ℝ | γ s ∈ A} =
        ⋃ k : ℤ, {s : ℝ | s - (k : ℝ) * (2 * Real.pi) ∈ P} := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      rw [hA]
      exact mem_image_iff_exists_period_sub_mem hper hinj
    rw [heq]
    exact isOpen_iUnion fun k => (hP ▸ isOpen_Ioo).preimage (by continuity)
  -- The complement of `A` inside the curve is the image of a compact parameter set, hence closed.
  have hKclosed : IsClosed (Set.range γ \ A) := by
    have hK : Set.range γ \ A =
        γ '' ({s : ℝ | γ s ∈ A}ᶜ ∩ Set.Icc 0 (2 * Real.pi)) := by
      ext y
      constructor
      · intro hy
        rw [Set.mem_sdiff] at hy
        obtain ⟨hyR, hyA⟩ := hy
        obtain ⟨s, rfl⟩ := hyR
        obtain ⟨k, hk⟩ := exists_int_sub_period_mem_Ico s
        have hper' : γ (s - (k : ℝ) * (2 * Real.pi)) = γ s := by
          have hh := (hper.int_mul k) (s - (k : ℝ) * (2 * Real.pi))
          rw [show s - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = s by ring] at hh
          exact hh.symm
        exact ⟨s - (k : ℝ) * (2 * Real.pi),
          ⟨by simpa [hper'] using hyA, Set.Ico_subset_Icc_self hk⟩, hper'⟩
      · rintro ⟨s, ⟨hsT, _⟩, rfl⟩
        rw [Set.mem_sdiff]
        exact ⟨Set.mem_range_self s, hsT⟩
    rw [hK]
    exact ((IsCompact.of_isClosed_subset isCompact_Icc
      (hTopen.isClosed_compl.inter isClosed_Icc) Set.inter_subset_right).image hcont).isClosed
  have ht₀A : γ t₀ ∈ A := by
    rw [hA]
    exact ⟨t₀, by rw [hP]; exact ⟨by linarith, by linarith⟩, rfl⟩
  have hArange : A ⊆ Set.range γ := by
    rw [hA]
    exact Set.image_subset_range γ P
  refine ⟨(Set.range γ \ A)ᶜ, hKclosed.isOpen_compl, ?_, ?_⟩
  · exact fun h => h.2 ht₀A
  · ext y
    constructor
    · rintro ⟨hyO, hyR⟩
      by_contra hyA
      exact hyO ⟨hyR, hyA⟩
    · intro hyA
      exact ⟨fun h => h.2 hyA, hArange hyA⟩

end Work.EpsW
