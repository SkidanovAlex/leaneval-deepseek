import Mathlib

namespace Commons.Combinatorics.Additive.AP

/-- A chain `f 0, f 1, …, f (n+1)` (indexed by `Fin (n+2)`) with constant integer step `s`
is affine: `f ⟨j, _⟩ = f ⟨0, _⟩ + s * j` for every `j < n + 2`. -/
private lemma chain_affine {n : ℕ} (f : Fin (n + 2) → ℤ) (s : ℤ)
    (hstep : ∀ j : Fin (n + 1), f j.succ - f (j.castSucc : Fin (n + 2)) = s) :
    ∀ (j : ℕ) (hj : j < n + 2), f ⟨j, hj⟩ = f ⟨0, by omega⟩ + s * (j : ℤ) := by
  intro j
  induction j with
  | zero =>
      intro hj
      have h0 : (⟨0, hj⟩ : Fin (n + 2)) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp
      simp [h0]
  | succ k ih =>
      intro hj
      have hk1 : k < n + 1 := by omega
      have hk2 : k < n + 2 := by omega
      have hsu : (⟨k, hk1⟩ : Fin (n + 1)).succ = ⟨k + 1, hj⟩ := by
        apply Fin.ext; simp
      have hca : ((⟨k, hk1⟩ : Fin (n + 1)).castSucc : Fin (n + 2)) = ⟨k, hk2⟩ := by
        apply Fin.ext; simp
      have hstepk := hstep ⟨k, hk1⟩
      have hstepk' : f ⟨k + 1, hj⟩ - f ⟨k, hk2⟩ = s := by
        simpa [hsu, hca] using hstepk
      have hlin : f ⟨k + 1, hj⟩ = f ⟨k, hk2⟩ + s := by linarith
      have ih' : f ⟨k, hk2⟩ = f ⟨0, by omega⟩ + s * (k : ℤ) := ih hk2
      calc
        f ⟨k + 1, hj⟩ = f ⟨k, hk2⟩ + s := hlin
        _ = (f ⟨0, by omega⟩ + s * (k : ℤ)) + s := by rw [ih']
        _ = f ⟨0, by omega⟩ + s * (k + 1 : ℤ) := by ring

theorem exists_ap_of_cyclic_consecutive {n N : ℕ} {A : Finset ℕ} (a : Fin (n + 2) → ℕ)
    (haA : ∀ j : Fin (n + 2), a j ∈ A)
    (haN : ∀ j : Fin (n + 2), a j < N)
    (t : ZMod (2 * N + 1)) (ht : t ≠ 0)
    (hstep : ∀ j : Fin (n + 1),
      ((a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ) : ZMod (2 * N + 1)) = t) :
    ∃ c b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < n + 2 → c + b * j ∈ A := by
  classical
  let e : Fin (n + 1) → ℤ := fun j => (a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ)
  have he_t : ∀ j : Fin (n + 1), (e j : ZMod (2 * N + 1)) = t := by
    intro j
    simpa [e] using hstep j
  have hN : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.zero_le N)
  have heN : ∀ j : Fin (n + 1), |e j| < (N : ℤ) := by
    intro j
    have hp : (0 : ℤ) ≤ (a j.succ : ℤ) := by exact_mod_cast (Nat.zero_le (a j.succ))
    have hpN : (a j.succ : ℤ) < (N : ℤ) := by exact_mod_cast (haN j.succ)
    have hq : (0 : ℤ) ≤ (a (j.castSucc : Fin (n + 2)) : ℤ) := by
      exact_mod_cast (Nat.zero_le (a (j.castSucc : Fin (n + 2))))
    have hqN : (a (j.castSucc : Fin (n + 2)) : ℤ) < (N : ℤ) := by
      exact_mod_cast (haN (j.castSucc : Fin (n + 2)))
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  have hcast : ((2 * N + 1 : ℕ) : ℤ) = (2 : ℤ) * (N : ℤ) + 1 := by norm_num
  have he_eq : ∀ j k : Fin (n + 1), e j = e k := by
    intro j k
    have hsub : (e j : ZMod (2 * N + 1)) - (e k : ZMod (2 * N + 1)) = 0 := by
      rw [he_t j, he_t k, sub_self]
    have hz : ((e j - e k : ℤ) : ZMod (2 * N + 1)) = 0 := by
      simpa using hsub
    have hdvd : ((2 * N + 1 : ℕ) : ℤ) ∣ e j - e k := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e j - e k) (2 * N + 1)).mp hz
    have habs : |e j - e k| < ((2 * N + 1 : ℕ) : ℤ) := by
      rw [hcast, abs_sub_lt_iff]
      constructor
      · linarith [(abs_lt.mp (heN j)).2, (abs_lt.mp (heN k)).1, hN]
      · linarith [(abs_lt.mp (heN j)).1, (abs_lt.mp (heN k)).2, hN]
    have hd : e j - e k = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact sub_eq_zero.mp hd
  let e0 : Fin (n + 1) := ⟨0, by omega⟩
  let s : ℤ := e e0
  have he_s : ∀ j : Fin (n + 1), e j = s := by
    intro j
    simpa [s] using he_eq j e0
  have hsn : s ≠ 0 := by
    intro hs0
    apply ht
    calc
      t = (e e0 : ZMod (2 * N + 1)) := (he_t e0).symm
      _ = 0 := by
        rw [he_s e0, hs0]
        simp
  have hstep_int : ∀ j : Fin (n + 1),
      (a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ) = s := by
    intro j
    simpa [e] using he_s j
  by_cases hpos : 0 < s
  · -- increasing chain
    let f0 : Fin (n + 2) := ⟨0, by omega⟩
    let b : ℕ := s.toNat
    have hbZ : (b : ℤ) = s := by
      dsimp [b]
      exact Int.toNat_of_nonneg (le_of_lt hpos)
    have hb : 1 ≤ b := by
      have hb1 : (1 : ℤ) ≤ (b : ℤ) := by
        rw [hbZ]
        linarith
      exact_mod_cast hb1
    have hstepN : ∀ (k : ℕ) (hk1 : k < n + 1) (hk3 : k + 1 < n + 2) (hk2 : k < n + 2),
        a ⟨k + 1, hk3⟩ = a ⟨k, hk2⟩ + b := by
      intro k hk1 hk3 hk2
      have hz := hstep_int ⟨k, hk1⟩
      have hsu : (⟨k, hk1⟩ : Fin (n + 1)).succ = ⟨k + 1, hk3⟩ := by
        apply Fin.ext; simp
      have hca : ((⟨k, hk1⟩ : Fin (n + 1)).castSucc : Fin (n + 2)) = ⟨k, hk2⟩ := by
        apply Fin.ext; simp
      have hrelZ : (a ⟨k + 1, hk3⟩ : ℤ) = (a ⟨k, hk2⟩ : ℤ) + s := by
        have hz' : (a ⟨k + 1, hk3⟩ : ℤ) - (a ⟨k, hk2⟩ : ℤ) = s := by
          simpa [hsu, hca] using hz
        linarith
      have hI : ((a ⟨k + 1, hk3⟩ : ℕ) : ℤ) = ((a ⟨k, hk2⟩ + b : ℕ) : ℤ) := by
        rw [hrelZ]
        rw [Nat.cast_add]
        rw [← hbZ]
      exact_mod_cast hI
    have hmem : ∀ (j : ℕ) (hj : j < n + 2), a ⟨j, hj⟩ = a f0 + b * j := by
      intro j
      induction j with
      | zero =>
          intro hj
          have h0 : (⟨0, hj⟩ : Fin (n + 2)) = f0 := by
            apply Fin.ext; simp [f0]
          simp [h0]
      | succ k ih =>
          intro hj
          have hk1 : k < n + 1 := by omega
          have hk2 : k < n + 2 := by omega
          have ih' : a ⟨k, hk2⟩ = a f0 + b * k := ih hk2
          calc
            a ⟨k + 1, hj⟩ = a ⟨k, hk2⟩ + b := hstepN k hk1 hj hk2
            _ = (a f0 + b * k) + b := by rw [ih']
            _ = a f0 + b * (k + 1) := by ring
    refine ⟨a f0, b, hb, ?_⟩
    intro j hj
    have hm := hmem j hj
    rw [← hm]
    exact haA ⟨j, hj⟩
  · -- decreasing chain
    have hneg : s < 0 := by omega
    let f0 : Fin (n + 2) := ⟨0, by omega⟩
    let flast : Fin (n + 2) := ⟨n + 1, by omega⟩
    let b : ℕ := (-s).toNat
    have hbZ : (b : ℤ) = -s := by
      dsimp [b]
      exact Int.toNat_of_nonneg (by linarith)
    have hb : 1 ≤ b := by
      have hb1 : (1 : ℤ) ≤ (b : ℤ) := by
        rw [hbZ]
        linarith
      exact_mod_cast hb1
    let af : Fin (n + 2) → ℤ := fun j => (a j : ℤ)
    have hsucZ : ∀ j : Fin (n + 1), af j.succ - af (j.castSucc : Fin (n + 2)) = s := by
      intro j
      simpa [af] using hstep_int j
    have haff := chain_affine af s hsucZ
    have hflast : flast = ⟨n + 1, by omega⟩ := by ext; simp [flast]
    have h1 : (a flast : ℤ) = (a f0 : ℤ) + s * ((n + 1 : ℕ) : ℤ) := by
      have hz := haff (n + 1) (by omega)
      simpa [af, hflast, f0] using hz
    have hmem : ∀ (j : ℕ) (hj : j < n + 2), a flast + b * j = a ⟨n + 1 - j, by omega⟩ := by
      intro j hj
      have hjle : j ≤ n + 1 := by omega
      have hk : n + 1 - j < n + 2 := by omega
      have h2 : (a ⟨n + 1 - j, hk⟩ : ℤ) = (a f0 : ℤ) + s * ((n + 1 - j : ℕ) : ℤ) := by
        simpa [af, f0] using haff (n + 1 - j) hk
      have hI : ((a flast + b * j : ℕ) : ℤ) = (a ⟨n + 1 - j, hk⟩ : ℤ) := by
        calc
          ((a flast + b * j : ℕ) : ℤ) = (a flast : ℤ) + ((b * j : ℕ) : ℤ) := by rw [Nat.cast_add]
          _ = (a flast : ℤ) + (b : ℤ) * (j : ℤ) := by rw [Nat.cast_mul]
          _ = ((a f0 : ℤ) + s * ((n + 1 : ℕ) : ℤ)) + (-s) * (j : ℤ) := by rw [h1, hbZ]
          _ = (a f0 : ℤ) + (s * ((n + 1 : ℕ) : ℤ) - s * (j : ℤ)) := by ring
          _ = (a f0 : ℤ) + s * (((n + 1 : ℕ) : ℤ) - (j : ℤ)) := by ring
          _ = (a f0 : ℤ) + s * ((n + 1 - j : ℕ) : ℤ) := by rw [Nat.cast_sub hjle]
          _ = (a ⟨n + 1 - j, hk⟩ : ℤ) := by rw [h2]
      have hNat : a flast + b * j = a ⟨n + 1 - j, hk⟩ := by
        exact_mod_cast hI
      have hfin : (⟨n + 1 - j, hk⟩ : Fin (n + 2)) = ⟨n + 1 - j, by omega⟩ := by
        apply Fin.ext; rfl
      rw [hfin] at hNat
      exact hNat
    refine ⟨a flast, b, hb, ?_⟩
    intro j hj
    have hm := hmem j hj
    rw [hm]
    exact haA ⟨n + 1 - j, by omega⟩

end Commons.Combinatorics.Additive.AP
