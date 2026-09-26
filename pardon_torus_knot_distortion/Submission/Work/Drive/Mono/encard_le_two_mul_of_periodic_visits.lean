import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Drive.Mono

open Set

noncomputable section

/-- Reduction of a real number modulo `2π` into the half-open interval `[0, 2π)`. -/
private def red (t : ℝ) : ℝ := 2 * Real.pi * Int.fract (t / (2 * Real.pi))

private lemma red_add_floor (t : ℝ) : red t + 2 * Real.pi * ⌊t / (2 * Real.pi)⌋ = t := by
  have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h1 : Int.fract (t / (2 * Real.pi)) = t / (2 * Real.pi) - ⌊t / (2 * Real.pi)⌋ := rfl
  rw [red, h1]
  field_simp
  ring

private lemma red_mem (t : ℝ) : red t ∈ Set.Ico 0 (2 * Real.pi) := by
  rw [red]
  refine ⟨mul_nonneg (by positivity) (Int.fract_nonneg _), ?_⟩
  have h := Int.fract_lt_one (t / (2 * Real.pi))
  nlinarith [Real.pi_pos]

private lemma red_self {t : ℝ} (h : t ∈ Set.Ico 0 (2 * Real.pi)) : red t = t := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : 0 ≤ t / (2 * Real.pi) := div_nonneg h.1 hT.le
  have h2 : t / (2 * Real.pi) < 1 := (div_lt_one hT).mpr h.2
  have hf : ⌊t / (2 * Real.pi)⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h1, h2⟩
  have hfr : Int.fract (t / (2 * Real.pi)) = t / (2 * Real.pi) := by
    rw [show Int.fract (t / (2 * Real.pi)) = t / (2 * Real.pi) - ⌊t / (2 * Real.pi)⌋ from rfl, hf]
    ring
  rw [red, hfr]
  field_simp

private lemma red_add_int (t : ℝ) (m : ℤ) : red (t + 2 * Real.pi * m) = red t := by
  have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [red, red]
  have h1 : (t + 2 * Real.pi * (m : ℝ)) / (2 * Real.pi) = t / (2 * Real.pi) + (m : ℝ) := by
    field_simp
  rw [h1, Int.fract_add_intCast]

private lemma red_sub_floor (t : ℝ) : red t = t - 2 * Real.pi * ⌊t / (2 * Real.pi)⌋ := by
  have := red_add_floor t
  linarith

/-- A set invariant under `t ↦ t + 2π` is invariant under every integer multiple. -/
private lemma mem_add_int {S : Set ℝ}
    (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ S ↔ t ∈ S) (t : ℝ) (m : ℤ) :
    t + 2 * Real.pi * m ∈ S ↔ t ∈ S := by
  have hper' : Function.Periodic (fun x : ℝ => x ∈ S) (2 * Real.pi) := fun x => propext (hper x)
  have h := hper'.int_mul m
  have h' := h t
  simpa [mul_comm] using h'

private lemma mem_shift (z a : ℝ) (X : Set ℝ) :
    z + a ∈ (fun x : ℝ => x + a) '' X ↔ z ∈ X := by
  rw [Set.mem_image]
  constructor
  · rintro ⟨y, hy, hyz⟩
    have : y = z := by linarith
    rwa [this] at hy
  · intro hz; exact ⟨z, hz, rfl⟩

/-- The defining relation of the family `V`: shifting the parameter by `2π m` shifts the set. -/
private lemma V_shift_mem {C : Set ℝ} {V : ℝ → Set ℝ}
    (hCper : ∀ t : ℝ, t + 2 * Real.pi ∈ C ↔ t ∈ C)
    (hVper : ∀ c ∈ C, V (c + 2 * Real.pi) = (fun x : ℝ => x + 2 * Real.pi) '' V c)
    {c : ℝ} (hc : c ∈ C) :
    ∀ (m : ℤ) (x : ℝ), x + 2 * Real.pi * m ∈ V (c + 2 * Real.pi * m) ↔ x ∈ V c := by
  intro m
  induction m using Int.induction_on with
  | zero => intro x; simp
  | succ i ih =>
      intro x
      have hmem : c + 2 * Real.pi * ((i : ℤ) : ℝ) ∈ C :=
        (mem_add_int hCper c (i : ℤ)).mpr hc
      have h1 : (c + 2 * Real.pi * ((i : ℤ) : ℝ)) + 2 * Real.pi
          = c + 2 * Real.pi * (((i : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
      have h2 : (x + 2 * Real.pi * ((i : ℤ) : ℝ)) + 2 * Real.pi
          = x + 2 * Real.pi * (((i : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [← h1, ← h2, hVper (c + 2 * Real.pi * ((i : ℤ) : ℝ)) hmem, mem_shift]
      exact ih x
  | pred i ih =>
      intro x
      have hmem : c + 2 * Real.pi * (((-(i : ℤ) - 1 : ℤ)) : ℝ) ∈ C :=
        (mem_add_int hCper c (-(i : ℤ) - 1)).mpr hc
      have h1 : (c + 2 * Real.pi * (((-(i : ℤ) - 1 : ℤ)) : ℝ)) + 2 * Real.pi
          = c + 2 * Real.pi * ((-(i : ℤ) : ℤ) : ℝ) := by push_cast; ring
      have h2 : (x + 2 * Real.pi * (((-(i : ℤ) - 1 : ℤ)) : ℝ)) + 2 * Real.pi
          = x + 2 * Real.pi * ((-(i : ℤ) : ℤ) : ℝ) := by push_cast; ring
      have key : x + 2 * Real.pi * ((-(i : ℤ) : ℤ) : ℝ)
            ∈ V (c + 2 * Real.pi * ((-(i : ℤ) : ℤ) : ℝ)) ↔
          x + 2 * Real.pi * (((-(i : ℤ) - 1 : ℤ)) : ℝ)
            ∈ V (c + 2 * Real.pi * (((-(i : ℤ) - 1 : ℤ)) : ℝ)) := by
        rw [← h1, ← h2, hVper (c + 2 * Real.pi * (((-(i : ℤ) - 1 : ℤ)) : ℝ)) hmem, mem_shift]
      rw [← key]
      exact ih x

private lemma V_shift_image {C : Set ℝ} {V : ℝ → Set ℝ}
    (hCper : ∀ t : ℝ, t + 2 * Real.pi ∈ C ↔ t ∈ C)
    (hVper : ∀ c ∈ C, V (c + 2 * Real.pi) = (fun x : ℝ => x + 2 * Real.pi) '' V c)
    {b : ℝ} (hb : b ∈ C) (m : ℤ) :
    V (b + 2 * Real.pi * m) = (fun x : ℝ => x + 2 * Real.pi * m) '' V b := by
  ext z
  rw [Set.mem_image]
  constructor
  · intro hz
    refine ⟨z - 2 * Real.pi * m, ?_, by ring⟩
    have hz' : (z - 2 * Real.pi * m) + 2 * Real.pi * m ∈ V (b + 2 * Real.pi * m) := by
      have : (z - 2 * Real.pi * m) + 2 * Real.pi * m = z := by ring
      rwa [this]
    exact (V_shift_mem hCper hVper hb m (z - 2 * Real.pi * m)).mp hz'
  · rintro ⟨y, hy, rfl⟩
    exact (V_shift_mem hCper hVper hb m y).mpr hy

/-- A point of `closure (V (b + 2π m))` lies, after subtracting `2π m`, in `closure (V b)`. -/
private lemma mem_closure_shift {C : Set ℝ} {V : ℝ → Set ℝ}
    (hCper : ∀ t : ℝ, t + 2 * Real.pi ∈ C ↔ t ∈ C)
    (hVper : ∀ c ∈ C, V (c + 2 * Real.pi) = (fun x : ℝ => x + 2 * Real.pi) '' V c)
    {b : ℝ} (hb : b ∈ C) (m : ℤ) {p : ℝ}
    (hp : p ∈ closure (V (b + 2 * Real.pi * m))) :
    p - 2 * Real.pi * m ∈ closure (V b) := by
  have hset := V_shift_image hCper hVper hb m
  have hcl : closure (V (b + 2 * Real.pi * m))
      = (fun x : ℝ => x + 2 * Real.pi * m) '' closure (V b) := by
    rw [hset]
    exact (Homeomorph.image_closure (Homeomorph.addRight (2 * Real.pi * m)) (V b)).symm
  rw [hcl, Set.mem_image] at hp
  obtain ⟨y, hy, hyx⟩ := hp
  rwa [show p - 2 * Real.pi * m = y by linarith]

open Set in
/-- If a `2π`-periodic set `P` is covered by the closures of the sets `V c` for `c` in a
`2π`-periodic `C`, each of which meets a `2π`-periodic `P'` in at most `2` points, then `P`
meets a period window `[0, 2π)` in at most `2` points per class of `C`.

Only the periodicity and the local bound `hloc` are used; `hlen` is not needed. -/
theorem encard_le_two_mul_of_periodic_visits
    {P P' C : Set ℝ} (hsub : P ⊆ P')
    (hP'per : ∀ t : ℝ, t + 2 * Real.pi ∈ P' ↔ t ∈ P')
    (hCper : ∀ t : ℝ, t + 2 * Real.pi ∈ C ↔ t ∈ C)
    (hCfin : (C ∩ Set.Ico 0 (2 * Real.pi)).Finite)
    (V : ℝ → Set ℝ)
    (hVper : ∀ c ∈ C, V (c + 2 * Real.pi) = (fun x : ℝ => x + 2 * Real.pi) '' V c)
    (hcover : ∀ p ∈ P, ∃ c ∈ C, p ∈ closure (V c))
    (hloc : ∀ c ∈ C, (P' ∩ closure (V c)).encard ≤ 2)
    (hlen : ∀ c ∈ C, ∀ x ∈ closure (V c), ∀ y ∈ closure (V c), ∀ k : ℤ, k ≠ 0 →
      y - x ≠ 2 * Real.pi * (k : ℝ)) :
    (P ∩ Set.Ico 0 (2 * Real.pi)).encard ≤ 2 * (C ∩ Set.Ico 0 (2 * Real.pi)).encard := by
  set B : Set ℝ := C ∩ Set.Ico 0 (2 * Real.pi) with hB
  set A : Set ℝ := P ∩ Set.Ico 0 (2 * Real.pi) with hA
  have hBfin : B.Finite := by rw [hB]; exact hCfin
  haveI : Fintype B := hBfin.fintype
  -- Every point of `A` reduces, modulo `2π`, into the reduced image of one of the `V b`, `b ∈ B`.
  have key : A ⊆ ⋃ b : B, red '' (P' ∩ closure (V (b : ℝ))) := by
    intro p hp
    rw [hA] at hp
    obtain ⟨hpP, hpI⟩ := hp
    obtain ⟨c, hcC, hpc⟩ := hcover p hpP
    -- `red c` still lies in `C`, and in `[0, 2π)`
    have hbc : red c ∈ C := by
      have h := (mem_add_int hCper c (-⌊c / (2 * Real.pi)⌋)).mpr hcC
      have hrc : red c = c + 2 * Real.pi * (((-⌊c / (2 * Real.pi)⌋ : ℤ)) : ℝ) := by
        rw [red_sub_floor]; push_cast; ring
      rwa [hrc]
    have hbB : red c ∈ B := by
      rw [hB]; exact ⟨hbc, red_mem c⟩
    -- `p - 2π⌊c/2π⌋` lies in `P' ∩ closure (V (red c))` and has the same reduction as `p`
    have hy_mem : p - 2 * Real.pi * ⌊c / (2 * Real.pi)⌋ ∈ P' ∩ closure (V (red c)) := by
      refine ⟨?_, ?_⟩
      · have hpP' : p ∈ P' := hsub hpP
        have h := (mem_add_int hP'per p (-⌊c / (2 * Real.pi)⌋)).mpr hpP'
        have hry : p + 2 * Real.pi * (((-⌊c / (2 * Real.pi)⌋ : ℤ)) : ℝ)
            = p - 2 * Real.pi * ⌊c / (2 * Real.pi)⌋ := by push_cast; ring
        rwa [hry] at h
      · have hpc' : p ∈ closure (V (red c + 2 * Real.pi * ⌊c / (2 * Real.pi)⌋)) := by
          have hrc : red c + 2 * Real.pi * ⌊c / (2 * Real.pi)⌋ = c := red_add_floor c
          rwa [hrc]
        exact mem_closure_shift hCper hVper hbc ⌊c / (2 * Real.pi)⌋ hpc'
    have hred_eq : red (p - 2 * Real.pi * ⌊c / (2 * Real.pi)⌋) = p := by
      have h1 : p - 2 * Real.pi * ⌊c / (2 * Real.pi)⌋
          = p + 2 * Real.pi * (((-⌊c / (2 * Real.pi)⌋ : ℤ)) : ℝ) := by push_cast; ring
      rw [h1, red_add_int]
      exact red_self hpI
    exact Set.mem_iUnion.mpr
      ⟨⟨red c, hbB⟩, ⟨p - 2 * Real.pi * ⌊c / (2 * Real.pi)⌋, hy_mem, hred_eq⟩⟩
  calc A.encard
      ≤ (⋃ b : B, red '' (P' ∩ closure (V (b : ℝ)))).encard := Set.encard_le_encard key
    _ ≤ ∑ b : B, (red '' (P' ∩ closure (V (b : ℝ)))).encard :=
        Set.encard_iUnion_le_of_fintype _
    _ ≤ ∑ _b : B, (2 : ℕ∞) :=
        Finset.sum_le_sum (fun b _ =>
          (Set.encard_image_le red _).trans (hloc (b : ℝ) b.2.1))
    _ = 2 * B.encard := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Set.coe_fintypeCard, mul_comm]
    _ = 2 * (C ∩ Set.Ico 0 (2 * Real.pi)).encard := by rw [hB]

end

end Work.Drive.Mono
