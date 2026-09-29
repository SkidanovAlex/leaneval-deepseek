import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.digits_Pcr

/-!
# The CRT reindexing `Pcr` commutes with the cyclic subtraction `subIdx`

`Pcr ss m` is the flat lexicographic index of the residue vector `(m % s₁, …, m % s_d)`
(`Work.Main.Pcr`), and `HvdH.subIdx ts j k` is the flat index of the componentwise
difference of the multi-indices of `j` and `k` (`HvdH.subDigits`/`HvdH.undigits`).

This file proves the arithmetic heart of the Agarwal–Cooley reindexing in §5.2 of
Harvey–van der Hoeven: for `m₁, m₂ < ∏ ss` and positive moduli `ss`,

  `subIdx ss (Pcr ss m₁) (Pcr ss m₂) = Pcr ss ((m₁ + ∏ss - m₂) % ∏ss)`,

i.e. composing the CRT embedding `Pcr` with the (cyclic) subtraction of multi-indices
is the same as subtracting the integers and re-embedding.  (Note that no coprimality
of the moduli is used: the identity is purely a mixed-radix statement.)

The proof is a chain of the following four ingredients, all in this file:

* `digits_Pcr` (previous file): `digits ss (Pcr ss m) = ss.map (m % ·)` — `Pcr` really
  encodes the residue vector;
* `subDigits_map_mod` : `subDigits` on vectors of the shape `ss.map f` and `ss.map g`
  is again given componentwise, by `(f s + s - g s) % s`;
* `mod_sub_prod` : the residues of `m₁ + ∏ss - m₂` are the componentwise differences,
  `(m₁ + ∏ss - m₂) % s = (m₁ % s + s - m₂ % s) % s` for every `s ∣ ∏ss`;
* `undigits_map_mod` : `undigits ss (ss.map (fun s => m % s)) = Pcr ss m` — `Pcr` is
  `undigits` of the residue vector.
-/

set_option autoImplicit false

namespace Work.Main.crt

open Work.Main

/-! ### Unfoldings of the two mixed-radix helpers -/

/-- Unfolding of `HvdH.undigits` on two conses. -/
lemma undigits_cons (t : ℕ) (ts js : List ℕ) (j : ℕ) :
    HvdH.undigits (t :: ts) (j :: js) = j * ts.prod + HvdH.undigits ts js := rfl

/-- Unfolding of `HvdH.subDigits` on two conses. -/
lemma subDigits_cons (t : ℕ) (ts js ks : List ℕ) (j k : ℕ) :
    HvdH.subDigits (t :: ts) (j :: js) (k :: ks) =
      (j + t - k) % t :: HvdH.subDigits ts js ks := rfl

/-! ### `undigits` of a residue vector is `Pcr` -/

/-- `Pcr ss m` is `undigits ss` applied to the residue vector `(m % s)`. -/
lemma undigits_map_mod (ss : List ℕ) (m : ℕ) :
    HvdH.undigits ss (ss.map (fun s => m % s)) = Pcr ss m := by
  induction ss with
  | nil => rfl
  | cons t ts ih => rw [List.map_cons, undigits_cons, Pcr_cons, ih]

/-! ### `subDigits` of a vector of residues -/

/-- `subDigits` acts componentwise on vectors given as `ss.map f`, `ss.map g`. -/
lemma subDigits_map_mod (ss : List ℕ) (f g : ℕ → ℕ) :
    HvdH.subDigits ss (ss.map f) (ss.map g) = ss.map (fun s => (f s + s - g s) % s) := by
  induction ss with
  | nil => rfl
  | cons t ts ih => rw [List.map_cons, List.map_cons, subDigits_cons, ih]; rfl

/-! ### Residues of `m₁ + P - m₂` -/

/-- The residues of `m₁ + P - m₂` are the componentwise differences of the residues of `m₁`
and `m₂`, for any modulus `s` dividing `P` (and `m₂ ≤ P`, so that the subtraction is exact). -/
lemma mod_sub_prod {m₁ m₂ P s : ℕ} (hs0 : 0 < s) (hP : m₂ ≤ P) (hs : s ∣ P) :
    (m₁ + P - m₂) % s = (m₁ % s + s - m₂ % s) % s := by
  have h1 : m₁ + P - m₂ = m₁ + (P - m₂) := by omega
  rw [h1, Nat.add_mod]
  have h2 : (P - m₂) % s = (s - m₂ % s) % s := by
    have hPa : P ≡ 0 [MOD s] := Nat.modEq_zero_iff_dvd.mpr hs
    have hsz : s ≡ 0 [MOD s] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    exact Nat.ModEq.sub hP (le_of_lt (Nat.mod_lt m₂ hs0)) (hPa.trans hsz.symm)
      (Nat.mod_modEq m₂ s).symm
  rw [h2]
  have h3 : m₁ % s + s - m₂ % s = m₁ % s + (s - m₂ % s) := by
    have := Nat.mod_lt m₂ hs0; omega
  rw [h3]
  exact Nat.ModEq.add_left _ (Nat.mod_modEq (s - m₂ % s) s)

/-! ### The main identity -/

theorem subIdx_Pcr {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {m₁ m₂ : ℕ} (h₁ : m₁ < ss.prod) (h₂ : m₂ < ss.prod) :
    HvdH.subIdx ss (Pcr ss m₁) (Pcr ss m₂) = Pcr ss ((m₁ + ss.prod - m₂) % ss.prod) := by
  rw [HvdH.subIdx, digits_Pcr hpos m₁, digits_Pcr hpos m₂, subDigits_map_mod]
  have hmap : ss.map (fun s => (m₁ % s + s - m₂ % s) % s)
      = ss.map (fun s => (m₁ + ss.prod - m₂) % s) := by
    apply List.map_congr_left
    intro s hs
    exact (mod_sub_prod (hpos s hs) (le_of_lt h₂) (List.dvd_prod hs)).symm
  rw [hmap, undigits_map_mod]
  exact (Pcr_mod_prod ss (m₁ + ss.prod - m₂)).symm

end Work.Main.crt
