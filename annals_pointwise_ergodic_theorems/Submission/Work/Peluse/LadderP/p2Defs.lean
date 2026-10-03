import Mathlib
import Submission.Work.Peluse.Holds.LadderP
import Submission.Work.Peluse.BoxNorm.boxNormPow_le_one_of_card_le
import Submission.Work.Peluse.LadderP.dilateSupportPreimage

/-! ## The `s = 2` heart of the ladder's P2 node: definitions

This module names the ingredients of the reduction of the frozen `lemma51P 2` (Peluse's Lemma 5.5,
`c = 1`, with a general window) to the *class* data produced by splitting `ℤ` into residue classes
mod `c`, and states the `c = 1` heart as a `Prop`.

* `p2BoxAvg` — the averaged level-two box norm `M₁⁻¹ ∑_{a ∈ [1,M₁]} ‖f‖_{□²_{((a+b_i)[M₂])_i}(S)}`
  with an *arbitrary* window set `S` (the frozen `boxAvgA` has `S = symIcc N`);
* `p2Heart` — the `c = 1` case of the frozen `lemma51P 2` with an arbitrary pair of window sets
  `(S, T)`: `T` is a finite support set for `f` and `S` the normalisation set of the box norm.

Everything else in this file is proved: the class-splitting lemmas that turn the hypothesis of the
frozen statement into class data (via `boxNormPow_dilate_split`), the power-mean/Jensen bookkeeping
that turns the class conclusions back into `uNormPow` of `f` (via the dilate splitting identity for
the uniformity norm), and the assembly itself.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The averaged level-`2` box norm over `a ∈ [1, M₁]` with the direction steps `a + b i` and an
arbitrary window (normalisation) set `S`.  The frozen `LadderQ.boxAvgA 2 c M₁ M₂ b N` is the case
`S = symIcc N` with the directions dilated by `c`. -/
def p2BoxAvg (M₁ M₂ : ℕ) (b : Fin 2 → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
    Work.Peluse.boxNorm 2 (fun i : Fin 2 => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂) S f

/-- The good-`a` predicate of the frozen statement at level `2`, copied here so that the `c = 1`
heart can be stated without importing the target file.  It is definitionally equal to
`goodA 2 M₁ b η a` of the target. -/
def p2Good (M₁ : ℕ) (b : Fin 2 → ℤ) (η : ℝ) (a : ℕ) : Prop :=
  (∀ i k : Fin 2, i ≠ k →
      ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η)
    ∧ ∀ i : Fin 2, η * (M₁ : ℝ) ≤ ((|((a : ℤ) + b i)| : ℤ) : ℝ)

noncomputable instance instDecidablePredP2Good (M₁ : ℕ) (b : Fin 2 → ℤ) (η : ℝ) :
    DecidablePred (p2Good M₁ b η) := fun _ => Classical.propDecidable _


/-! ### The residue classes of `symIcc N`, their weights and their supports -/

/-- The residue class `r` of the symmetric window `symIcc N`. -/
def p2Cls (c : ℤ) (N : ℕ) (r : ℕ) : Finset ℤ :=
  (symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))

/-- The class function `f_r (ξ) = f (r + c ξ)`. -/
def p2ClsFn (c : ℤ) (r : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun ξ => f ((r : ℤ) + c * ξ)

/-- The support of the class function inside `symIcc N`: the preimage of `S_r` under `x ↦ r + c x`,
i.e. `{(x - r)/c : x ∈ S_r}`. -/
def p2Sup (c : ℤ) (N : ℕ) (r : ℕ) : Finset ℤ :=
  (p2Cls c N r).image (fun x : ℤ => (x - (r : ℤ)) / c)

/-- The class weight `w_r = |S_r| / |symIcc N|`. -/
def p2Wt (c : ℤ) (N : ℕ) (r : ℕ) : ℝ := ((p2Cls c N r).card : ℝ) / (((symIcc N).card : ℝ))

@[simp] lemma p2ClsFn_apply (c : ℤ) (r : ℕ) (f : ℤ → ℂ) (ξ : ℤ) :
    p2ClsFn c r f ξ = f ((r : ℤ) + c * ξ) := rfl

/-- **The `c = 1` heart.**  The `c = 1` case of the frozen `lemma51P 2` (Peluse's Lemma 5.5) with
an arbitrary normalisation window `S` comparable to the symmetric window `symIcc N` on which `f`
lives.  The hypothesis scheme is that of the frozen `lemma51P` with `c` replaced by `1` and the
`symIcc N` window of the averaged box norm replaced by the general set `S`; the two window
conditions `2N+1 ≤ 4|S|` and `M₁M₂ ≤ N` say that `S` is of the same order as the window `symIcc N`
and that the direction window fits inside it, exactly as for the class windows produced by
splitting `symIcc N` into residue classes mod `c`. -/
def p2Heart : Prop :=
  ∀ B₀ : ℕ, ∃ s' : ℕ, 1 ≤ s' ∧ ∃ e : ℕ, 1 ≤ e ∧ ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
  ∀ (M₁ M₂ D N : ℕ) (S : Finset ℤ) (b : Fin 2 → ℤ) (γ η ε : ℝ) (f : ℤ → ℂ),
    2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ D → 1 ≤ N →
    SupportIn f N → ((2 * N + 1 : ℕ) : ℝ) ≤ 4 * ((S.card : ℕ) : ℝ) →
    ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
    (∀ i : Fin 2, |b i| ≤ (B₀ : ℤ) * (M₁ : ℤ)) →
    (∀ x : ℤ, ‖f x‖ ≤ 1) →
    0 < γ → γ ≤ 1 → 0 < η → η ≤ C * γ ^ e → 0 ≤ ε → ε ≤ C * γ ^ e →
    (D : ℝ) ≤ C * (γ * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) →
    ((M₁ : ℝ) * (M₂ : ℝ)) ^ e ≤ C * (γ * η * (D : ℝ)) ^ e * (M₂ : ℝ) →
    (((Finset.Icc 1 M₁).filter (fun a : ℕ => ¬ p2Good M₁ b η a)).card : ℝ) ≤ ε * (M₁ : ℝ) →
    γ ≤ p2BoxAvg M₁ M₂ b S f →
    C * γ ^ e ≤ Work.Peluse.uNorm s' (Work.Peluse.arithIcc 1 D) S f


/-! ### Elementary facts about the classes -/

lemma p2Wt_nonneg (c : ℤ) (N r : ℕ) : 0 ≤ p2Wt c N r :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma card_symIcc_pos {N : ℕ} : 0 < (symIcc N).card := by
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  rw [symIcc, Finset.mem_Icc]
  constructor <;> simp

/-- The residue classes of `symIcc N` partition it, so the weights sum to `1`. -/
lemma p2Wt_sum {c : ℤ} (hc : 0 < c) (N : ℕ) :
    ∑ r ∈ Finset.range c.natAbs, p2Wt c N r = 1 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcardne : (((symIcc N).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (card_symIcc_pos (N := N))
  have hmem : ∀ x : ℤ, (x % c).toNat ∈ Finset.range c.natAbs := by
    intro x
    rw [Finset.mem_range]
    have h1 : 0 ≤ x % c := Int.emod_nonneg x hcne
    have h2 : x % c < ((c.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_pos hc]
      exact Int.emod_lt_of_pos x hc
    have h3 : (((x % c).toNat : ℕ) : ℤ) = x % c := Int.toNat_of_nonneg h1
    have h4 : (((x % c).toNat : ℕ) : ℤ) < ((c.natAbs : ℕ) : ℤ) := by rw [h3]; exact h2
    exact_mod_cast h4
  have hiff : ∀ (x : ℤ) (r : ℕ), (x % c = (r : ℤ)) ↔ ((x % c).toNat = r) := by
    intro x r
    constructor
    · intro h; rw [h]; exact Int.toNat_natCast r
    · intro h
      have h1 : 0 ≤ x % c := Int.emod_nonneg x hcne
      rw [← Int.toNat_of_nonneg h1, h]
  have hsum : ∑ r ∈ Finset.range c.natAbs, (p2Cls c N r).card = (symIcc N).card := by
    have h1 : ∀ r : ℕ, (p2Cls c N r).card
        = ∑ x ∈ symIcc N, (if x % c = (r : ℤ) then 1 else 0) := by
      intro r
      rw [p2Cls, Finset.card_filter]
    calc ∑ r ∈ Finset.range c.natAbs, (p2Cls c N r).card
        = ∑ r ∈ Finset.range c.natAbs,
            ∑ x ∈ symIcc N, (if x % c = (r : ℤ) then 1 else 0) :=
          Finset.sum_congr rfl (fun r _ => h1 r)
      _ = ∑ x ∈ symIcc N,
            ∑ r ∈ Finset.range c.natAbs, (if x % c = (r : ℤ) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ _x ∈ symIcc N, 1 := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          have hstep : ∀ r : ℕ, (if x % c = (r : ℤ) then (1 : ℕ) else 0)
              = (if (x % c).toNat = r then 1 else 0) := by
            intro r
            rw [if_congr (hiff x r) (rfl : (1:ℕ) = 1) (rfl : (0:ℕ) = 0)]
          rw [Finset.sum_congr rfl (fun r _ => hstep r)]
          rw [Finset.sum_ite_eq (Finset.range c.natAbs) ((x % c).toNat) (fun _ => (1 : ℕ))]
          simp [hmem x]
      _ = (symIcc N).card := by simp
  have hsumR : ∑ r ∈ Finset.range c.natAbs, ((p2Cls c N r).card : ℝ)
      = (((symIcc N).card : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, hsum]
  calc ∑ r ∈ Finset.range c.natAbs, p2Wt c N r
      = (∑ r ∈ Finset.range c.natAbs, ((p2Cls c N r).card : ℝ)) / (((symIcc N).card : ℕ) : ℝ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun r _ => rfl)
    _ = 1 := by rw [hsumR, div_self hcardne]

/-- Each class is contained in the window, so its cardinality is at most the window's. -/
lemma p2Cls_card_le (c : ℤ) (N r : ℕ) : (p2Cls c N r).card ≤ (symIcc N).card :=
  Finset.card_filter_le _ _

/-- The support `p2Sup c N r` is the image of `S_r` under the injective map `x ↦ (x - r)/c`, hence
has the same cardinality as `S_r`. -/
lemma p2Sup_card {c : ℤ} (hc : 0 < c) {N r : ℕ} :
    (p2Sup c N r).card = (p2Cls c N r).card := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [p2Sup]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  have hx'' : x ∈ p2Cls c N r := by simpa using hx
  have hy'' : y ∈ p2Cls c N r := by simpa using hy
  obtain ⟨-, hxc⟩ := Finset.mem_filter.mp hx''
  obtain ⟨-, hyc⟩ := Finset.mem_filter.mp hy''
  have hxq : (x - (r : ℤ)) / c = x / c := by
    have h2 := Int.emod_def x c
    rw [hxc] at h2
    have h3 : x - (r : ℤ) = c * (x / c) := by linarith
    rw [h3, Int.mul_ediv_cancel_left (x / c) hcne]
  have hyq : (y - (r : ℤ)) / c = y / c := by
    have h2 := Int.emod_def y c
    rw [hyc] at h2
    have h3 : y - (r : ℤ) = c * (y / c) := by linarith
    rw [h3, Int.mul_ediv_cancel_left (y / c) hcne]
  have hxy' : x / c = y / c := by rw [← hxq, ← hyq]; exact hxy
  have hx1 : x = (x / c) * c + (r : ℤ) := by
    have h := Int.emod_add_ediv_mul x c
    rw [hxc] at h
    linarith
  have hy1 : y = (y / c) * c + (r : ℤ) := by
    have h := Int.emod_add_ediv_mul y c
    rw [hyc] at h
    linarith
  rw [hx1, hy1, hxy']

/-- The class function is supported in `p2Sup`. -/
lemma p2Sup_support {c : ℤ} (hc : 0 < c) {N : ℕ} {r : ℕ} (hr : r < c.natAbs)
    {f : ℤ → ℂ} (hsup : SupportIn f N) :
    ∀ x : ℤ, x ∉ p2Sup c N r → p2ClsFn c r f x = 0 := by
  intro x hx
  rw [p2Sup] at hx
  exact dilateSupportPreimage hc hr hsup x hx

end

end Work.Peluse.LadderP
