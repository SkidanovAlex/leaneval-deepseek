import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# A field structure from a cyclic regular action (Singer cycle)

This module supplies `Work.PSU3.StageA.cyclic_regular_action_field`: a finite group `V` of
exponent `2` on which a cyclic group of automorphisms of order `|V| - 1` acts regularly on the
non-identity elements carries a field structure of cardinality `|V|` whose addition is the group
law of `V`, the automorphisms acting by multiplication.

Mathematically: a Singer cycle `g` on the `𝔽₂`-space `V` turns `V` into `GF(2 ^ m)` on which `g`
is multiplication by a primitive element; the construction is explicit: for `x ≠ 1` write
`x = g ^ i e` with `e` a fixed non-identity element and put `x · y = g ^ i y`.

The helper lemmas `orbit_fix_eq_one` and `pow_eq_of_apply_eq_of_orbit` record the two
consequences of regularity used below: an automorphism commuting with `g` and fixing one
non-identity element of the orbit is the identity, and two powers of `g` agreeing on `e`
coincide.
-/

namespace Work.PSU3.StageA

variable {V : Type*} [Group V]

/-- An automorphism commuting with `g` which fixes an element of the orbit `g ^ · e` different
from `1` is the identity. -/
theorem orbit_fix_eq_one {g h : MulAut V} (hcomm : h * g = g * h)
    {e : V} (htrans : ∀ v : V, v ≠ 1 → ∃ i : ℕ, (g ^ i) e = v)
    {x : V} (hx : x ≠ 1) (hfix : h x = x) : h = 1 := by
  have hcomm_pow : ∀ i : ℕ, h * g ^ i = g ^ i * h := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc h * g ^ (i + 1) = h * (g ^ i * g) := by rw [pow_succ]
        _ = (h * g ^ i) * g := by rw [mul_assoc]
        _ = (g ^ i * h) * g := by rw [ih]
        _ = g ^ i * (h * g) := by rw [mul_assoc]
        _ = g ^ i * (g * h) := by rw [hcomm]
        _ = (g ^ i * g) * h := by rw [mul_assoc]
        _ = g ^ (i + 1) * h := by rw [pow_succ]
  obtain ⟨i, hi⟩ := htrans x hx
  have hee : h e = e := by
    apply (g ^ i).injective
    calc (g ^ i) (h e) = (g ^ i * h) e := by rw [MulAut.mul_apply]
      _ = (h * g ^ i) e := by rw [hcomm_pow i]
      _ = h ((g ^ i) e) := by rw [MulAut.mul_apply]
      _ = h x := by rw [hi]
      _ = x := hfix
      _ = (g ^ i) e := hi.symm
  apply MulEquiv.ext
  intro v
  by_cases hv : v = 1
  · rw [hv, map_one]; rfl
  · obtain ⟨j, hj⟩ := htrans v hv
    calc h v = h ((g ^ j) e) := by rw [hj]
      _ = (h * g ^ j) e := by rw [MulAut.mul_apply]
      _ = (g ^ j * h) e := by rw [hcomm_pow j]
      _ = (g ^ j) (h e) := by rw [MulAut.mul_apply]
      _ = (g ^ j) e := by rw [hee]
      _ = v := hj
      _ = (1 : MulAut V) v := rfl

/-- Two natural-number powers of `g` which agree on `e` are equal. -/
theorem pow_eq_of_apply_eq_of_orbit {g : MulAut V} {e : V} (he : e ≠ 1)
    (htrans : ∀ v : V, v ≠ 1 → ∃ i : ℕ, (g ^ i) e = v)
    {i j : ℕ} (hij : (g ^ i) e = (g ^ j) e) : g ^ i = g ^ j := by
  have hei : (g ^ i) e ≠ 1 := fun h => he ((g ^ i).injective (by rw [h, map_one]))
  have hcomm : ∀ k : ℕ, g ^ k * g = g * g ^ k := fun k => by
    simpa using pow_mul_comm g k 1
  rcases le_total i j with hle | hle
  · have hfix : (g ^ (j - i)) ((g ^ i) e) = (g ^ i) e := by
      calc (g ^ (j - i)) ((g ^ i) e) = (g ^ (j - i) * g ^ i) e := by rw [MulAut.mul_apply]
        _ = (g ^ (j - i + i)) e := by rw [pow_add]
        _ = (g ^ j) e := by rw [Nat.sub_add_cancel hle]
        _ = (g ^ i) e := hij.symm
    have h1 : g ^ (j - i) = 1 := orbit_fix_eq_one (hcomm (j - i)) htrans hei hfix
    calc g ^ i = g ^ i * 1 := (mul_one _).symm
      _ = g ^ i * g ^ (j - i) := by rw [h1]
      _ = g ^ (i + (j - i)) := by rw [pow_add]
      _ = g ^ j := by rw [Nat.add_sub_cancel' hle]
  · have hfix : (g ^ (i - j)) ((g ^ j) e) = (g ^ j) e := by
      calc (g ^ (i - j)) ((g ^ j) e) = (g ^ (i - j) * g ^ j) e := by rw [MulAut.mul_apply]
        _ = (g ^ (i - j + j)) e := by rw [pow_add]
        _ = (g ^ i) e := by rw [Nat.sub_add_cancel hle]
        _ = (g ^ j) e := hij
    have h1 : g ^ (i - j) = 1 := orbit_fix_eq_one (hcomm (i - j)) htrans
      (fun h => he ((g ^ j).injective (by rw [h, map_one]))) hfix
    calc g ^ i = g ^ (i - j + j) := by rw [Nat.sub_add_cancel hle]
      _ = g ^ (i - j) * g ^ j := by rw [pow_add]
      _ = 1 * g ^ j := by rw [h1]
      _ = g ^ j := one_mul _

/-- **Singer cycle.** A cyclic group of automorphisms of a finite group of exponent `2` acting
regularly on the non-identity elements makes that group into a field (of the same cardinality)
on which the automorphisms act by multiplication. -/
theorem cyclic_regular_action_field {V : Type} [Group V] [Fintype V] [DecidableEq V]
    {K : Type} [Group K]
    (h2 : ∀ x : V, x * x = 1) (act : K →* MulAut V) (k₀ : K) (e : V) (he : e ≠ 1)
    (hspan : ∀ k : K, ∃ j : ℕ, act k = act k₀ ^ j)
    (hord : orderOf (act k₀) = Nat.card V - 1)
    (htrans : ∀ v : V, v ≠ 1 → ∃ i : ℕ, (act k₀ ^ i) e = v) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (φ : V ≃ F) (ρ : K →* Fˣ),
      Nat.card F = Nat.card V ∧ (∀ a b : V, φ (a * b) = φ a + φ b) ∧
      (∀ (k : K) (v : V), φ (act k v) = (ρ k : F) * φ v) := by
  classical
  let g : MulAut V := act k₀
  have htrans' : ∀ v : V, v ≠ 1 → ∃ i : ℕ, (g ^ i) e = v := htrans
  have hkey : ∀ i j : ℕ, (g ^ i) e = (g ^ j) e → g ^ i = g ^ j :=
    fun i j hij => pow_eq_of_apply_eq_of_orbit he htrans' hij
  have gpow_ne_one : ∀ i : ℕ, (g ^ i) e ≠ 1 := fun i h =>
    he ((g ^ i).injective (by rw [h, map_one]))
  let idx : (x : V) → x ≠ 1 → ℕ := fun x hx => Classical.choose (htrans x hx)
  have idx_spec : ∀ (x : V) (hx : x ≠ 1), (g ^ idx x hx) e = x :=
    fun x hx => Classical.choose_spec (htrans x hx)
  let m : V → V → V := fun x y => if hx : x = 1 then 1 else (g ^ idx x hx) y
  let minv : V → V := fun x => if hx : x = 1 then 1 else (g ^ idx x hx)⁻¹ e
  have m_def : ∀ x y : V, m x y = (if hx : x = 1 then (1 : V) else (g ^ idx x hx) y) :=
    fun x y => rfl
  have minv_def : ∀ x : V, minv x = (if hx : x = 1 then (1 : V) else (g ^ idx x hx)⁻¹ e) :=
    fun x => rfl
  have m_of_ne : ∀ {x y : V} (hx : x ≠ 1), m x y = (g ^ idx x hx) y := by
    intro x y hx
    rw [m_def, dif_neg hx]
  have minv_of_ne : ∀ {x : V} (hx : x ≠ 1), minv x = (g ^ idx x hx)⁻¹ e := by
    intro x hx
    rw [minv_def, dif_neg hx]
  have m_one_left : ∀ y : V, m 1 y = 1 := by
    intro y
    rw [m_def, dif_pos rfl]
  have m_one_right : ∀ x : V, m x 1 = 1 := by
    intro x
    by_cases hx : x = 1
    · rw [hx, m_one_left]
    · rw [m_of_ne hx]; exact map_one _
  have m_spec : ∀ {x y : V} (hx : x ≠ 1) (i : ℕ), (g ^ i) e = x → m x y = (g ^ i) y := by
    intro x y hx i hi
    rw [m_of_ne hx]
    exact congrArg (fun (f : MulAut V) => f y) (hkey _ _ (by rw [idx_spec x hx, hi]))
  have m_ne_one : ∀ {x y : V}, x ≠ 1 → y ≠ 1 → m x y ≠ 1 := by
    intro x y hx hy h
    have h1 : (g ^ idx x hx) y = 1 := by rw [← m_of_ne hx, h]
    exact hy ((g ^ idx x hx).injective (by rw [h1, map_one]))
  have m_eq_one_iff : ∀ x y : V, m x y = 1 ↔ x = 1 ∨ y = 1 := by
    intro x y
    constructor
    · intro h
      by_cases hx : x = 1
      · exact Or.inl hx
      · refine Or.inr ?_
        have h1 : (g ^ idx x hx) y = 1 := by rw [← m_of_ne hx, h]
        exact (g ^ idx x hx).injective (by rw [h1, map_one])
    · rintro (rfl | rfl)
      · exact m_one_left y
      · exact m_one_right x
  have m_comm : ∀ x y : V, m x y = m y x := by
    intro x y
    by_cases hx : x = 1
    · rw [hx, m_one_left, m_one_right]
    · by_cases hy : y = 1
      · rw [hy, m_one_left, m_one_right]
      · obtain ⟨i, hi⟩ := htrans x hx
        obtain ⟨j, hj⟩ := htrans y hy
        calc m x y = (g ^ i) y := m_spec hx i hi
          _ = (g ^ i) ((g ^ j) e) := by rw [← hj]
          _ = (g ^ (i + j)) e := by rw [← MulAut.mul_apply, ← pow_add]
          _ = (g ^ (j + i)) e := by rw [Nat.add_comm]
          _ = (g ^ j) ((g ^ i) e) := by rw [pow_add, MulAut.mul_apply]
          _ = (g ^ j) x := by rw [← hi]
          _ = m y x := (m_spec hy j hj).symm
  have m_assoc : ∀ x y z : V, m (m x y) z = m x (m y z) := by
    intro x y z
    by_cases hx : x = 1
    · rw [hx, m_one_left]
      exact (m_one_left z).trans (m_one_left (m y z)).symm
    · by_cases hy : y = 1
      · rw [hy]; simp only [m_one_right, m_one_left]
      · by_cases hz : z = 1
        · rw [hz]; simp only [m_one_right]
        · obtain ⟨i, hi⟩ := htrans x hx
          obtain ⟨j, hj⟩ := htrans y hy
          obtain ⟨k, hk⟩ := htrans z hz
          have hmxy : m x y = (g ^ (i + j)) e := by
            rw [m_spec hx i hi, ← hj, pow_add, MulAut.mul_apply]
          have hmyz : m y z = (g ^ (j + k)) e := by
            rw [m_spec hy j hj, ← hk, pow_add, MulAut.mul_apply]
          have hmxy_ne : m x y ≠ 1 := by rw [hmxy]; exact gpow_ne_one _
          calc m (m x y) z = (g ^ (i + j)) z := m_spec hmxy_ne (i + j) hmxy.symm
            _ = (g ^ (i + j)) ((g ^ k) e) := by rw [← hk]
            _ = (g ^ (i + j + k)) e := by rw [← MulAut.mul_apply, ← pow_add]
            _ = (g ^ (i + (j + k))) e := by rw [Nat.add_assoc]
            _ = (g ^ i) ((g ^ (j + k)) e) := by rw [pow_add, MulAut.mul_apply]
            _ = (g ^ i) (m y z) := by rw [← hmyz]
            _ = m x (m y z) := (m_spec hx i hi).symm
  have m_distrib : ∀ x y z : V, m x (y * z) = m x y * m x z := by
    intro x y z
    by_cases hx : x = 1
    · rw [hx, m_one_left, m_one_left, m_one_left, one_mul]
    · rw [m_of_ne hx, m_of_ne hx, m_of_ne hx, map_mul]
  have h_idx_e : g ^ idx e he = 1 := by
    have h := hkey (idx e he) 0 (by rw [idx_spec e he, pow_zero, MulAut.one_apply])
    rwa [pow_zero] at h
  have m_one_mul : ∀ y : V, m e y = y := by
    intro y
    by_cases hy : y = 1
    · rw [hy, m_one_right]
    · rw [m_of_ne he, h_idx_e, MulAut.one_apply]
  have minv_zero : minv 1 = 1 := by
    rw [minv_def, dif_pos rfl]
  have m_mul_minv : ∀ x : V, x ≠ 1 → m x (minv x) = e := by
    intro x hx
    rw [m_of_ne hx, minv_of_ne hx, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  letI hMul : Mul (Additive V) := ⟨fun a b => Additive.ofMul (m a.toMul b.toMul)⟩
  letI hOne : One (Additive V) := ⟨Additive.ofMul e⟩
  letI hInv : Inv (Additive V) := ⟨fun a => Additive.ofMul (minv a.toMul)⟩
  have hMul_ofMul : ∀ p q : V,
      (Additive.ofMul p : Additive V) * Additive.ofMul q = Additive.ofMul (m p q) :=
    fun p q => rfl
  have hOne_ofMul : (Additive.ofMul e : Additive V) = 1 := rfl
  have hInv_ofMul : ∀ p : V, (Additive.ofMul p : Additive V)⁻¹ = Additive.ofMul (minv p) :=
    fun p => rfl
  letI hF : Field (Additive V) :=
    Field.ofMinimalAxioms (Additive V)
      (fun a b c => add_assoc a b c)
      (fun a => zero_add a)
      (fun a => neg_add_cancel a)
      (fun a b c => by
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        obtain ⟨y, rfl⟩ := Additive.ofMul.surjective b
        obtain ⟨z, rfl⟩ := Additive.ofMul.surjective c
        simp only [hMul_ofMul, m_assoc])
      (fun a b => by
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        obtain ⟨y, rfl⟩ := Additive.ofMul.surjective b
        simp only [hMul_ofMul, m_comm])
      (fun a => by
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        simp only [← hOne_ofMul, hMul_ofMul, m_one_mul])
      (fun a ha => by
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        have hx : x ≠ 1 := fun h1 => ha (by rw [h1, ofMul_one])
        simp only [hInv_ofMul, hMul_ofMul, m_mul_minv x hx, hOne_ofMul])
      (by
        change (Additive.ofMul (1 : V) : Additive V)⁻¹ = Additive.ofMul (1 : V)
        rw [hInv_ofMul, minv_zero])
      (fun a b c => by
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        obtain ⟨y, rfl⟩ := Additive.ofMul.surjective b
        obtain ⟨z, rfl⟩ := Additive.ofMul.surjective c
        simp only [hMul_ofMul, ← ofMul_mul, m_distrib])
      ⟨Additive.ofMul e, Additive.ofMul 1, fun h => he (Additive.ofMul.injective h)⟩
  have hρ_ne : ∀ k : K, (Additive.ofMul (act k e) : Additive V) ≠ 0 := by
    intro k h
    rw [ofMul_eq_zero] at h
    exact he ((act k).injective (by rw [h, map_one]))
  have hequiv : ∀ (k : K) (v : V),
      Additive.ofMul (act k v) = Additive.ofMul (act k e) * Additive.ofMul v := by
    intro k v
    obtain ⟨j, hj⟩ := hspan k
    rw [hj]
    by_cases hv : v = 1
    · subst hv
      rw [map_one, ofMul_one]
      show Additive.ofMul (1 : V) = Additive.ofMul (m ((g ^ j) e) 1)
      rw [m_one_right]
    · obtain ⟨i, hi⟩ := htrans v hv
      have hspec : m ((g ^ j) e) v = (g ^ j) v := m_spec (gpow_ne_one j) j rfl
      rw [← hspec, hMul_ofMul]
  let ρ : K →* (Additive V)ˣ :=
    { toFun := fun k => Units.mk0 (Additive.ofMul (act k e)) (hρ_ne k)
      map_one' := by
        apply Units.ext
        show Additive.ofMul (act 1 e) = (1 : Additive V)
        rw [map_one, MulAut.one_apply, hOne_ofMul]
      map_mul' := fun k₁ k₂ => by
        apply Units.ext
        simp only [Units.val_mk0]
        rw [map_mul, MulAut.mul_apply]
        exact hequiv k₁ (act k₂ e) }
  exact ⟨Additive V, hF, inferInstance, Additive.ofMul, ρ, Nat.card_congr Additive.ofMul,
    (fun a b => rfl), hequiv⟩

end Work.PSU3.StageA
