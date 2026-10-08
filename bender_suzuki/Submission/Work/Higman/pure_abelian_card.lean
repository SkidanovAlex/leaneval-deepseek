import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- For a homomorphism of groups, `|ker f| * |range f| = |G|`. -/
private lemma card_ker_mul_card_range {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  have h := Subgroup.card_mul_index f.ker
  rwa [Subgroup.index_ker f] at h

/-- **Pure group theory.**  A finite abelian 2-group `A` in which all involutions have the same
height (the explicit dichotomy hypothesis: if some non-trivial involution is a `2 ^ s`-th power,
then *every* involution is a `2 ^ s`-th power) is homocyclic: if its exponent is `2 ^ E` then
`|A| = |A[2]| ^ E`, where `A[2]` is the set of elements with `x ^ 2 = 1`. -/
theorem pure_abelian_card
    (A : Type*) [CommGroup A] [Finite A] (h2 : IsPGroup 2 A)
    (hdich : ∀ (s : ℕ) (x : A), x ^ 2 = 1 → x ≠ 1 → (∃ y : A, y ^ 2 ^ s = x) →
      ∀ z : A, z ^ 2 = 1 → ∃ y : A, y ^ 2 ^ s = z)
    (E : ℕ) (hE1 : ∀ a : A, a ^ 2 ^ E = 1) (hE2 : ∃ a : A, orderOf a = 2 ^ E) :
    Nat.card A = (Nat.card {x : A | x ^ 2 = 1}) ^ E := by
  -- `K = A[2]`, the subgroup of involutions.
  let K : Subgroup A := (powMonoidHom (α := A) 2).ker
  -- `Om j = A[2^j]`, the elements whose `2 ^ j`-th power is one.
  let Om : ℕ → Subgroup A := fun j => (powMonoidHom (α := A) (2 ^ j)).ker
  have hKmem : ∀ x : A, x ∈ K ↔ x ^ 2 = 1 := by
    intro x; simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hOmmem : ∀ (j : ℕ) (x : A), x ∈ Om j ↔ x ^ 2 ^ j = 1 := by
    intro j x; simp [Om, MonoidHom.mem_ker, powMonoidHom_apply]
  -- The dichotomy: for `j ≤ E - 1` every involution is a `2 ^ j`-th power.
  have hdich_apply : ∀ j, j + 1 ≤ E → ∀ z : A, z ^ 2 = 1 → ∃ y : A, y ^ 2 ^ j = z := by
    intro j hj z hz
    obtain ⟨a, ha⟩ := hE2
    have hEpos : 1 ≤ E := by omega
    have haE : a ^ 2 ^ E = 1 := by
      have h := (orderOf_dvd_iff_pow_eq_one (x := a) (n := 2 ^ E))
      rw [ha] at h
      exact h.mp dvd_rfl
    have hexp : 2 ^ (E - 1) * 2 = 2 ^ E := by
      rw [← pow_succ, Nat.sub_add_cancel hEpos]
    -- `x₀ = a ^ (2 ^ (E - 1))` is a non-trivial involution which is a `2 ^ j`-th power.
    have hx0sq : (a ^ 2 ^ (E - 1)) ^ 2 = 1 := by
      rw [← pow_mul, hexp]; exact haE
    have hx0ne : a ^ 2 ^ (E - 1) ≠ 1 := by
      intro h
      have hdvd : 2 ^ E ∣ 2 ^ (E - 1) := by
        have hh := (orderOf_dvd_iff_pow_eq_one (x := a) (n := 2 ^ (E - 1))).mpr h
        rwa [ha] at hh
      have hpos : 0 < 2 ^ (E - 1) := pow_pos (by norm_num) _
      have hlt : 2 ^ (E - 1) < 2 ^ E := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hle := Nat.le_of_dvd hpos hdvd
      omega
    have hle : j ≤ E - 1 := by omega
    have hpow : ∃ y : A, y ^ 2 ^ j = a ^ 2 ^ (E - 1) := by
      refine ⟨a ^ 2 ^ (E - 1 - j), ?_⟩
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hle]
    exact hdich j (a ^ 2 ^ (E - 1)) hx0sq hx0ne hpow z hz
  have hOmmono : ∀ j, Om j ≤ Om (j + 1) := by
    intro j x hx
    rw [hOmmem] at hx ⊢
    calc x ^ 2 ^ (j + 1) = (x ^ 2 ^ j) ^ 2 := by rw [pow_succ, pow_mul]
      _ = 1 := by rw [hx, one_pow]
  -- The recurrence `|Om (j+1)| = |Om j| * |K|`.
  have step : ∀ j, j + 1 ≤ E → Nat.card ↥(Om (j + 1)) = Nat.card ↥(Om j) * Nat.card ↥K := by
    intro j hj
    let g : ↥(Om (j + 1)) →* A := (powMonoidHom (α := A) (2 ^ j)).comp (Om (j + 1)).subtype
    have hg : ∀ x : ↥(Om (j + 1)), g x = (x : A) ^ 2 ^ j := by
      intro x; simp [g, MonoidHom.comp_apply, Subgroup.subtype_apply, powMonoidHom_apply]
    have hrange : g.range = K := by
      apply le_antisymm
      · intro y hy
        rw [MonoidHom.mem_range] at hy
        obtain ⟨x, rfl⟩ := hy
        rw [hKmem, hg]
        calc ((x : A) ^ 2 ^ j) ^ 2 = (x : A) ^ 2 ^ (j + 1) := by rw [← pow_mul, ← pow_succ]
          _ = 1 := (hOmmem (j + 1) (x : A)).mp x.2
      · intro z hz
        rw [MonoidHom.mem_range]
        obtain ⟨y, hy⟩ := hdich_apply j hj z ((hKmem z).mp hz)
        refine ⟨⟨y, ?_⟩, ?_⟩
        · rw [hOmmem]
          calc y ^ 2 ^ (j + 1) = (y ^ 2 ^ j) ^ 2 := by rw [pow_succ, pow_mul]
            _ = 1 := by rw [hy, (hKmem z).mp hz]
        · simpa [hg] using hy
    have hmap : Subgroup.map (Om (j + 1)).subtype g.ker = Om j := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h1 : g y = 1 := (MonoidHom.mem_ker).mp hy
        rw [hg] at h1
        rw [hOmmem]
        exact h1
      · intro hx
        rw [hOmmem] at hx
        refine ⟨⟨x, hOmmono j hx⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker, hg]
        exact hx
    have hker : Nat.card ↥(g.ker) = Nat.card ↥(Om j) := by
      calc Nat.card ↥(g.ker)
          = Nat.card ↥(Subgroup.map (Om (j + 1)).subtype g.ker) :=
            (Subgroup.card_subtype (Om (j + 1)) g.ker).symm
        _ = Nat.card ↥(Om j) := by rw [hmap]
    calc Nat.card ↥(Om (j + 1)) = Nat.card ↥(g.ker) * Nat.card ↥(g.range) :=
          (card_ker_mul_card_range g).symm
      _ = Nat.card ↥(Om j) * Nat.card ↥K := by rw [hker, hrange]
  have hbase : Nat.card ↥(Om 0) = Nat.card ↥K ^ 0 := by
    rw [pow_zero]
    have hbot : Om 0 = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      rw [hOmmem] at hx
      simpa using hx
    rw [hbot, Subgroup.card_bot]
  have hmain : Nat.card ↥(Om E) = Nat.card ↥K ^ E := by
    have key := Nat.le_induction (m := 0)
      (P := fun j _ => j ≤ E → Nat.card ↥(Om j) = Nat.card ↥K ^ j)
      (fun _ => hbase)
      (fun n _ ih hn1 => by
        rw [step n hn1, ih (by omega : n ≤ E), pow_succ])
      E (Nat.zero_le E)
    exact key le_rfl
  have hOmE : Om E = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [hOmmem]
    exact hE1 x
  have hcardA : Nat.card A = Nat.card ↥K ^ E := by
    rw [← Subgroup.card_top (G := A), ← hOmE]
    exact hmain
  have hKcard : Nat.card ↥K = Nat.card {x : A | x ^ 2 = 1} := by
    have hset : (K : Set A) = {x : A | x ^ 2 = 1} := by
      ext x; simpa using hKmem x
    exact congrArg (fun s : Set A => Nat.card ↥s) hset
  rw [hcardA, hKcard]

end Work.Higman
