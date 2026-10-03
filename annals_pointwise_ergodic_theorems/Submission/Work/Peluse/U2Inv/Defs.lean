import Mathlib
import Submission.Work.Peluse.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the `U²`-inverse theorem (Peluse's Lemma 2.4)

This module sets up the objects used in the proof of `Work.Peluse.PeluseU2Inverse`
(Peluse, *Bounds for sets with no polynomial progressions*, Forum Math. Pi **8** (2020),
Lemma 2.4), specialised to the interval form of the `U²` box norm used by the workspace.

The strategy of the proof: the interval box sum is rewritten as a weighted average of the
difference operators `Δ_{a,b} f` (the weight being Peluse's `μ_m`), which is then transported to
the cyclic group `ZMod (4L+1)`, where the discrete Fourier transform turns it into a sum of
"twisted" `U²` quantities `TT`; the classical `U²`-inverse argument (Cauchy–Schwarz in the
frequency variable) then produces a single character correlation.

## Main definitions

* `DeltaZ a b f x = conj (f (x+a)) * conj (f (x+b)) * f (x+a+b) * f x` — the second difference;
* `T3 L m f` — the `μ_m`-weighted `Δ`-sum over the interval `[-L,L]`;
* `Gmod L = 4L+1` — the modulus of the auxiliary cyclic group;
* `pF L f` — the zero extension of `f` to `ZMod (Gmod L)`;
* `nu L m` — the weight `μ_m` transported to `ZMod (Gmod L)`;
* `gW L m f`, `DeltaG`, `TT` — the group weighted `Δ`-sum and its Fourier transform in the shift
  variables.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-! ## The auxiliary group -/

/-- The modulus `4L+1` of the auxiliary cyclic group: it is strictly larger than `4L`, so that
all the differences `x - y` with `x` in the support of `f` and `y` in the support of the
truncated cube sum are represented faithfully modulo `Gmod L`. -/
def Gmod (L : ℕ) : ℕ := 4 * L + 1

instance instNeZeroGmod (L : ℕ) : NeZero (Gmod L) := ⟨by simp [Gmod]⟩

/-! ## Convenience lemmas about the index sets -/

lemma mem_symIcc_iff {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ -((L : ℤ)) ≤ x ∧ x ≤ (L : ℤ) :=
  Finset.mem_Icc

lemma symIcc_eq_Icc (L : ℕ) : symIcc L = Finset.Icc (-((L : ℤ))) (L : ℤ) := rfl

lemma card_symIcc (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc_eq_Icc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - -((L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

lemma mem_arithIcc_one_iff {m : ℕ} {x : ℤ} :
    x ∈ arithIcc 1 m ↔ ∃ n : ℕ, 1 ≤ n ∧ n ≤ m ∧ x = (n : ℤ) := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨n, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, by simp⟩
  · rintro ⟨n, h1, h2, rfl⟩
    refine Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨h1, h2⟩, by simp⟩

lemma card_arithIcc_one (m : ℕ) : (arithIcc 1 m).card = m := by
  rw [arithIcc, Finset.card_image_of_injective _ ?_]
  · simp
  · intro a b hab
    simpa using hab

/-! ## The interval difference operator and its weighted sum -/

/-- The second difference operator `Δ_{a,b} f (x) = conj (f (x+a)) * conj (f (x+b)) * f (x+a+b) * f x`
(Peluse's `Δ_{h₁,h₂}`, up to the order of the factors). -/
def DeltaZ (a b : ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => star (f (x + a)) * star (f (x + b)) * f (x + a + b) * f x

/-- The `μ_m`-weighted `Δ`-sum over the interval `[-L,L]`: the "interval form" that the box sum
`boxSumPow 2 (fun _ => arithIcc 1 m) (symIcc L) f` equals (up to the normalisation
`((symIcc L).card)⁻¹`). -/
def T3 (L m : ℕ) (f : ℤ → ℂ) : ℂ :=
  ∑ x ∈ symIcc L, ∑ a ∈ symIcc (m - 1), ∑ b ∈ symIcc (m - 1),
    (muL m a : ℂ) * (muL m b : ℂ) * DeltaZ a b f x

/-! ## The auxiliary group, the transported function and weight -/

/-- The zero extension of `f` to `ZMod (Gmod L)` (summed over the possible representatives
`a ∈ symIcc L`; this is a genuine single term because `a ↦ (a : ZMod (Gmod L))` is injective on
`symIcc L`). -/
def pF (L : ℕ) (f : ℤ → ℂ) : ZMod (Gmod L) → ℂ :=
  fun z => ∑ a ∈ symIcc L, if (a : ZMod (Gmod L)) = z then f a else 0

/-- Peluse's weight `μ_m`, transported to `ZMod (Gmod L)`: the distribution of `u - u'` for two
independent uniform points `u, u'` of `{1, …, m}` (viewed in the group). -/
def nu (L m : ℕ) : ZMod (Gmod L) → ℂ :=
  fun z => ((m : ℂ) ^ 2)⁻¹ *
    ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
      (fun p : ℕ × ℕ => ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) = z)).card : ℂ)

/-- The group difference operator `Δ_{a,b} F (x) = conj (F (x+a)) * conj (F (x+b)) * F (x+a+b) * F x`. -/
def DeltaG {N : ℕ} (a b : ZMod N) (F : ZMod N → ℂ) : ZMod N → ℂ :=
  fun x => star (F (x + a)) * star (F (x + b)) * F (x + a + b) * F x

/-- The group weighted `Δ`-sum (the average over `x, a, b ∈ ZMod (Gmod L)`). -/
def gW (L m : ℕ) (f : ℤ → ℂ) : ℂ :=
  (((Gmod L : ℂ)) ^ 3)⁻¹ * ∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
    nu L m a * nu L m b * DeltaG a b (pF L f) x

/-- The Fourier transform of the group weighted `Δ`-sum in the two shift variables `a, b`:
the "twisted `U²` quantity" whose maximum controls the weight via Fourier inversion. -/
def TT (L : ℕ) (k₁ k₂ : ZMod (Gmod L)) (F : ZMod (Gmod L) → ℂ) : ℂ :=
  (((Gmod L : ℂ)) ^ 3)⁻¹ * ∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
    DeltaG a b F x * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)

/-- The form of Peluse's `U²`-inverse theorem produced by the Fourier proof below (mirroring
`Work.Peluse.PeluseU2Inverse`, with the constant `C'` and exponent `K` explicit): the proof gives
`C' = 1/2`, `K = 2`, i.e. `|∑_x f x e(βx)| ≥ (δδ')²L/2`, which follows from the sharper bound
`|∑_x f x e(βx)| ≥ m δ²`, `m = ⌊δ'L⌋`. -/
def SharpU2Inverse : Prop :=
  ∃ C' : ℝ, 0 < C' ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (L : ℕ) (δ δ' : ℝ) (f : ℤ → ℂ),
      1 ≤ L → 0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
      SupportIn f L → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      δ ≤ uNorm 2 (arithIcc 1 ((⌊δ' * (L : ℝ)⌋).toNat)) (symIcc L) f →
      ∃ β : ℝ,
        C' * (δ * δ') ^ K * (L : ℝ) ≤
          ‖∑' x : ℤ, f x * Complex.exp (2 * Real.pi * Complex.I * β * x)‖

end

end Work.Peluse.U2Inv
