import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pcr_lt

/-!
# Injectivity of the Agarwal–Cooley CRT reindexing `Pcr`

`Pcr ss m = undigits ss (ss.map (m % ·))` is the flat lexicographic index of the multi-index
of residues `(m % s₁, …, m % s_d)`. This file proves that, when the moduli `ss` are pairwise
coprime and positive, `Pcr ss` is injective on the range `[0, ∏ ss)`.

The proof splits in three arithmetic ingredients, all in this file:

* `Pcr_mod_prod` : `Pcr ss` depends on `m` only through `m % ss.prod` (each `m % s` only
  depends on `m % ss.prod` since `s ∣ ss.prod`);
* `Pcr_residues` : if `Pcr ss m₁ = Pcr ss m₂` then `m₁ % s = m₂ % s` for every `s ∈ ss`
  (induction over the list, using the mixed-radix decomposition of `Pcr` and `Pcr_mod_prod`);
* `modEq_prod` + `coprime_prod_of_forall` : for pairwise coprime moduli,
  `m₁ % s = m₂ % s` for all `s ∈ ss` forces `m₁ ≡ m₂ [MOD ss.prod]`.

Injectivity then follows since both `m₁, m₂ < ss.prod`.
-/

set_option autoImplicit false

namespace Work.Main.crt

open Work.Main

/-- For pairwise coprime moduli `t, s₁, …, s_d` (given as `h`), `t` is coprime to the product
`ts.prod`. -/
theorem coprime_prod_of_forall {t : ℕ} {ts : List ℕ} (h : ∀ s ∈ ts, Nat.Coprime t s) :
    Nat.Coprime t ts.prod := by
  induction ts with
  | nil => simp
  | cons s ts ih =>
      rw [List.prod_cons]
      exact (h s (by simp)).mul_right (ih (fun a ha => h a (by simp [ha])))

/-- The flat CRT index only depends on the residue class of `m` modulo the product of the moduli:
`Pcr ss (m % ss.prod) = Pcr ss m`. -/
theorem Pcr_mod_prod (ss : List ℕ) (m : ℕ) : Pcr ss (m % ss.prod) = Pcr ss m := by
  induction ss generalizing m with
  | nil => rfl
  | cons t ts ih =>
      rw [List.prod_cons, Pcr_cons, Pcr_cons, Nat.mod_mod_of_dvd m (dvd_mul_right t ts.prod)]
      have e1 : m % (t * ts.prod) % ts.prod = m % ts.prod :=
        Nat.mod_mod_of_dvd m (dvd_mul_left ts.prod t)
      rw [← ih (m % (t * ts.prod)), e1, ih m]

/-- **Residue recovery.** If two integers have the same flat CRT index with respect to positive
pairwise coprime moduli, then they have the same residue modulo every modulus. (No bound on
`m₁, m₂` is needed.) -/
theorem Pcr_residues : ∀ (ss : List ℕ), ss.Pairwise Nat.Coprime → (∀ s ∈ ss, 0 < s) →
    ∀ m₁ m₂ : ℕ, Pcr ss m₁ = Pcr ss m₂ → ∀ s ∈ ss, m₁ % s = m₂ % s
  | [], _, _, _, _, _, s, hs => by simp at hs
  | t :: ts, hcop, hpos, m₁, m₂, h, s, hs => by
      rw [Pcr_cons, Pcr_cons] at h
      rw [List.pairwise_cons] at hcop
      obtain ⟨hcop_t, hcop_ts⟩ := hcop
      have hts : ∀ s ∈ ts, 0 < s := fun s hs => hpos s (by simp [hs])
      have hP : 0 < ts.prod := List.prod_pos hts
      have hp1 : Pcr ts m₁ < ts.prod := Pcr_lt hts m₁
      have hp2 : Pcr ts m₂ < ts.prod := Pcr_lt hts m₂
      -- the tail indices agree, being the `% ts.prod` of the common value
      have hX : Pcr ts m₁ = Pcr ts m₂ := by
        have h' := congrArg (· % ts.prod) h
        rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2] at h'
        exact h'
      rcases List.mem_cons.mp hs with hst | hs'
      · -- the leading residue: cancel the common factor `ts.prod`
        rw [hst]
        have hmul : (m₁ % t) * ts.prod = (m₂ % t) * ts.prod := by
          rw [hX] at h
          exact Nat.add_right_cancel h
        exact Nat.eq_of_mul_eq_mul_right hP hmul
      · -- the remaining residues: reduce both to `m % ts.prod` and apply the induction hypothesis
        have hIH : (m₁ % ts.prod) % s = (m₂ % ts.prod) % s :=
          Pcr_residues ts hcop_ts hts (m₁ % ts.prod) (m₂ % ts.prod)
            (by rw [Pcr_mod_prod ts m₁, Pcr_mod_prod ts m₂, hX]) s hs'
        rwa [Nat.mod_mod_of_dvd m₁ (List.dvd_prod hs'),
          Nat.mod_mod_of_dvd m₂ (List.dvd_prod hs')] at hIH

/-- Chinese remainder uniqueness, list form: if `x` and `y` have the same residue modulo every
element of a pairwise coprime list `ss`, then they are congruent modulo `ss.prod`. -/
theorem modEq_prod {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) {x y : ℕ}
    (h : ∀ s ∈ ss, x ≡ y [MOD s]) : x ≡ y [MOD ss.prod] := by
  induction ss with
  | nil => exact Nat.modEq_one
  | cons t ts ih =>
      rw [List.prod_cons]
      rw [List.pairwise_cons] at hcop
      obtain ⟨hcop_t, hcop_ts⟩ := hcop
      exact (Nat.modEq_and_modEq_iff_modEq_mul (coprime_prod_of_forall (t := t) hcop_t)).mp
        ⟨h t (by simp), ih hcop_ts (fun s hs => h s (by simp [hs]))⟩

/-- **`Pcr` is injective on `[0, ∏ ss)`** for pairwise coprime positive moduli `ss`:
the flat reindexing of the CRT residue vector loses no information. -/
theorem Pcr_inj {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {m₁ m₂ : ℕ} (h₁ : m₁ < ss.prod) (h₂ : m₂ < ss.prod) (h : Pcr ss m₁ = Pcr ss m₂) : m₁ = m₂ := by
  have hres : ∀ s ∈ ss, m₁ % s = m₂ % s := Pcr_residues ss hcop hpos m₁ m₂ h
  have hmod : m₁ % ss.prod = m₂ % ss.prod := modEq_prod hcop hres
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hmod

end Work.Main.crt
