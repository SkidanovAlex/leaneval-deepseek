import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Hering.AppVIII

/-- The support (within `{0, …, n-1}`) of a function `lam : ℕ → F` satisfying the
two "Singer-cycle" relations `h1`, `h3` is a single point.

The mathematical content is that, working modulo `n`, `h1` says
`lam x · lam (x - s)^(2^s) = 0`, i.e. the support `S` contains no two elements
differing by `s`; and `h3`, together with `h1`, forces `S ⊆ {x, x - 2s}` for every
`x ∈ S`.  Applying this twice and using `¬ n ∣ 4 * s` to exclude the two
degeneracies `2s ≡ 0` and `4s ≡ 0` gives `S = {x}`. -/
theorem supportSingleton {F : Type*} [Field F] {n s : ℕ} (hsn : s < n) (hs0 : s ≠ 0)
    (h4 : ¬ n ∣ 4 * s) (lam : ℕ → F) (hne : ∃ k < n, lam k ≠ 0)
    (h1 : ∀ k < n, lam k * (lam ((k + n - s) % n)) ^ (2 ^ s) = 0)
    (h3 : ∀ k < n, ∀ l < n, k ≠ l → (k + s) % n ≠ l → (l + s) % n ≠ k →
      lam k * (lam ((l + n - s) % n)) ^ (2 ^ s) + lam l * (lam ((k + n - s) % n)) ^ (2 ^ s) = 0) :
    ∃ i < n, lam i ≠ 0 ∧ ∀ j < n, j ≠ i → lam j = 0 := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  have hsle : s ≤ n := le_of_lt hsn
  -- Pass to residues modulo `n`.
  let f : ZMod n → F := fun c => lam c.val
  -- The representative of `c - s` is `(c.val + n - s) % n`.
  have hval_sub : ∀ c : ZMod n, (c - s).val = (c.val + n - s) % n := by
    intro c
    have hc : ((c.val : ℕ) : ZMod n) = c := ZMod.natCast_zmod_val c
    have hcs : ((c.val + n - s : ℕ) : ZMod n) = c - s := by
      rw [Nat.add_sub_assoc hsle, Nat.cast_add, Nat.cast_sub hsle, ZMod.natCast_self, hc]
      ring
    rw [← hcs, ZMod.val_natCast]
  -- `h1` restated on residues: `f c * f (c - s)^(2^s) = 0`.
  have A1 : ∀ c : ZMod n, f c * (f (c - s)) ^ (2 ^ s) = 0 := by
    intro c
    have h := h1 c.val (ZMod.val_lt c)
    simp only [f]
    rw [hval_sub c]
    exact h
  -- `h3` restated on residues.
  have A3 : ∀ c d : ZMod n, c ≠ d → c + s ≠ d → d + s ≠ c →
      f c * (f (d - s)) ^ (2 ^ s) + f d * (f (c - s)) ^ (2 ^ s) = 0 := by
    intro c d hcd hcs hds
    have hc : ((c.val : ℕ) : ZMod n) = c := ZMod.natCast_zmod_val c
    have hd : ((d.val : ℕ) : ZMod n) = d := ZMod.natCast_zmod_val d
    have hclt := ZMod.val_lt c
    have hdlt := ZMod.val_lt d
    have hsval : ((s : ℕ) : ZMod n).val = s := ZMod.val_cast_of_lt hsn
    have hne : c.val ≠ d.val := by
      intro h; exact hcd (by rw [← hc, ← hd, h])
    have h1' : (c.val + s) % n ≠ d.val := by
      intro h
      have : c + s = d := by
        apply ZMod.val_injective n
        rw [ZMod.val_add, hsval, h]
      exact hcs this
    have h2' : (d.val + s) % n ≠ c.val := by
      intro h
      have : d + s = c := by
        apply ZMod.val_injective n
        rw [ZMod.val_add, hsval, h]
      exact hds this
    have h := h3 c.val hclt d.val hdlt hne h1' h2'
    simp only [f]
    rw [hval_sub c, hval_sub d]
    exact h
  obtain ⟨k, hklt, hkne⟩ := hne
  set x : ZMod n := (k : ZMod n) with hxdef
  have hxval : x.val = k := by rw [hxdef, ZMod.val_cast_of_lt hklt]
  have hxne : f x ≠ 0 := by
    have : f x = lam k := by simp only [f, hxval]
    rw [this]; exact hkne
  -- `2s` and `4s` are nonzero modulo `n` because `n ∤ 4s`.
  have h2s : (2 : ZMod n) * (s : ZMod n) ≠ 0 := by
    intro h
    apply h4
    have hd : n ∣ 2 * s := by
      have hh : ((2 * s : ℕ) : ZMod n) = 0 := by rw [Nat.cast_mul, Nat.cast_ofNat]; exact h
      exact (ZMod.natCast_eq_zero_iff (2*s) n).mp hh
    exact dvd_trans hd ⟨2, by ring⟩
  have h4s : (4 : ZMod n) * (s : ZMod n) ≠ 0 := by
    intro h
    apply h4
    have hd : ((4 * s : ℕ) : ZMod n) = 0 := by rw [Nat.cast_mul, Nat.cast_ofNat]; exact h
    exact (ZMod.natCast_eq_zero_iff (4*s) n).mp hd
  -- **Key step.** For any nonzero `x'`, every `m ≠ x'` with `m + 2s ≠ x'` vanishes.
  have key : ∀ x' : ZMod n, f x' ≠ 0 → ∀ m : ZMod n, m ≠ x' → m + 2 * s ≠ x' → f m = 0 := by
    intro x' hx' m hm hm2
    have hxs : f (x' - s) = 0 := by
      have ha := A1 x'
      rw [mul_eq_zero] at ha
      rcases ha with h | h
      · exact absurd h hx'
      · exact (pow_eq_zero_iff').mp h |>.1
    by_cases hms : m = x' - s
    · rw [hms]; exact hxs
    · have hA : f x' * (f ((m + s) - s)) ^ (2 ^ s) + f (m + s) * (f (x' - s)) ^ (2 ^ s) = 0 :=
        A3 x' (m + s) (by intro hh; exact hms (by rw [hh]; ring))
          (by intro hh; exact hm (add_right_cancel hh).symm)
          (by intro hh; exact hm2 (by rw [← hh]; ring))
      have hsub : (m + s) - s = m := by ring
      have hz : (0 : F) ^ (2 ^ s) = 0 := zero_pow (by positivity)
      rw [hsub, hxs, hz, mul_zero, add_zero] at hA
      rw [mul_eq_zero] at hA
      rcases hA with h | h
      · exact absurd h hx'
      · exact (pow_eq_zero_iff').mp h |>.1
  -- The support is a single point.
  have hsupp : ∀ m : ZMod n, f m ≠ 0 → m = x := by
    intro m hm
    by_cases h2 : m + 2 * s = x
    · exfalso
      have hxm : x ≠ m := by
        intro hh
        have hmm : m + 2 * s = m := by rw [h2, hh]
        have hz : (2 : ZMod n) * (s : ZMod n) = 0 := by
          have hh2 := congrArg (fun t => t - m) hmm
          simpa using hh2
        exact h2s hz
      have hx2m : x + 2 * s ≠ m := by
        intro hh
        have hxx : x + 4 * s = x := by
          calc x + 4 * s = (x + 2 * s) + 2 * s := by ring
            _ = m + 2 * s := by rw [hh]
            _ = x := h2
        have hz : (4 : ZMod n) * (s : ZMod n) = 0 := by
          have hh2 := congrArg (fun t => t - x) hxx
          simpa using hh2
        exact h4s hz
      exact hxne (key m hm x hxm hx2m)
    · by_contra hne'
      exact hm (key x hxne m hne' h2)
  refine ⟨k, hklt, hkne, ?_⟩
  intro j hjlt hjne
  by_contra hj
  have hfj : f (j : ZMod n) ≠ 0 := by
    simp only [f]
    rwa [ZMod.val_cast_of_lt hjlt]
  have hjeq : (j : ZMod n) = x := hsupp (j : ZMod n) hfj
  have hjk : j = k := by
    have := congrArg ZMod.val hjeq
    rw [ZMod.val_cast_of_lt hjlt, hxval] at this
    exact this
  exact hjne hjk

end Work.Hering.AppVIII
