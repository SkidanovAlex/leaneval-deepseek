import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace Commons.GroupTheory.Cyclic

lemma card_fiber_eq_card_ker {G : Type*} [Group G] (f : G →* G) {m : G}
    (hm : m ∈ f.range) :
    Nat.card {x : G // f x = m} = Nat.card f.ker := by
  classical
  rcases (MonoidHom.mem_range).mp hm with ⟨x0, hx0⟩
  let fwd : {x : G // f x = m} → f.ker := fun x => ⟨x.1 * x0⁻¹, by
    rw [MonoidHom.mem_ker, f.map_mul, f.map_inv, x.2, hx0]
    simp⟩
  let bwd : f.ker → {x : G // f x = m} := fun k => ⟨k.1 * x0, by
    have hk : f k.1 = 1 := (MonoidHom.mem_ker).mp k.2
    rw [f.map_mul, hk, hx0]
    simp⟩
  let e : {x : G // f x = m} ≃ f.ker :=
    { toFun := fwd
      invFun := bwd
      left_inv := by
        intro x
        apply Subtype.ext
        simp [fwd, bwd, mul_assoc]
      right_inv := by
        intro k
        apply Subtype.ext
        simp [fwd, bwd, mul_assoc] }
  exact Nat.card_congr e

theorem fiber_card_pow_eq_of_pow_eq_one {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (a b : ℕ) (ha : 0 < a) (hcard : Nat.card G = b * a)
    (m : G) (hm : m ^ b = 1) :
    Nat.card {x : G // x ^ a = m} = a := by
  classical
  let f : G →* G := powMonoidHom a
  let g : G →* G := powMonoidHom b
  have hle : f.range ≤ g.ker := by
    rintro x ⟨y, hy⟩
    rw [MonoidHom.mem_ker]
    have hyx : x = y ^ a := by simpa [f] using hy.symm
    have hp : y ^ (a * b) = 1 := by
      have h := pow_card_eq_one' (x := y)
      rw [hcard, Nat.mul_comm] at h
      exact h
    calc
      x ^ b = (y ^ a) ^ b := by rw [hyx]
      _ = y ^ (a * b) := by rw [pow_mul]
      _ = 1 := hp
  have hkerb : Nat.card (g : G →* G).ker = b := by
    have h := IsCyclic.card_powMonoidHom_ker (G := G) b
    rw [hcard] at h
    have hg : (b * a).gcd b = b := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left (dvd_mul_right b a)
    rw [hg] at h
    simpa [g] using h
  have hrangea : Nat.card (f : G →* G).range = b := by
    have h := IsCyclic.card_powMonoidHom_range (G := G) a
    rw [hcard] at h
    have hg : (b * a).gcd a = a := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left (dvd_mul_left a b)
    rw [hg] at h
    have hdiv : b * a / a = b := Nat.mul_div_left b ha
    rw [hdiv] at h
    simpa [f] using h
  have hle_card : Nat.card (g : G →* G).ker ≤ Nat.card (f : G →* G).range := by
    rw [hkerb, hrangea]
  have hEq : f.range = g.ker := Subgroup.eq_of_le_of_card_ge hle hle_card
  have hm_ker : m ∈ g.ker := by
    rw [MonoidHom.mem_ker]
    exact hm
  have hm_range : m ∈ f.range := by
    rw [hEq]
    exact hm_ker
  calc
    Nat.card {x : G // x ^ a = m}
        = Nat.card {x : G // f x = m} := by rfl
    _ = Nat.card f.ker := card_fiber_eq_card_ker f hm_range
    _ = (Nat.card G).gcd a := by
        simpa [f] using (IsCyclic.card_powMonoidHom_ker (G := G) a)
    _ = a := by
        rw [hcard]
        rw [Nat.gcd_comm]
        exact Nat.gcd_eq_left (dvd_mul_left a b)

end Commons.GroupTheory.Cyclic