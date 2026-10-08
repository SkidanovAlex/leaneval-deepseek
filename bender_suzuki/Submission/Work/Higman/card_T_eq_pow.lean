import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The order of `Ω_j` in a finite abelian group of exponent dividing `2^e`

Let `A` be a finite abelian group and `Ω_j = {x : A | x ^ (2 ^ j) = 1}`.
If `A` has exponent dividing `2 ^ e` and `|A| = |Ω_1| ^ e`, then for every
`j ≤ e` one has `|Ω_j| = |Ω_1| ^ j`.

The proof rests on the elementary observation that the map
`Ω_{k+1} → Ω_1`, `x ↦ x ^ (2 ^ k)`, is a homomorphism whose kernel is
exactly `Ω_k`.  Hence `|Ω_{k+1}| ≤ |Ω_k| * |Ω_1|`, which gives both
`|Ω_j| ≤ |Ω_1| ^ j` and, multiplied along the chain `j, …, e` together
with `|Ω_e| = |A| = |Ω_1| ^ e`, the reverse inequality.
-/

namespace Work.Higman

section Basic

variable {A : Type*} [CommGroup A]

/-- `Ω_j`, the subgroup of elements whose order divides `2 ^ j`. -/
def omega (j : ℕ) : Subgroup A where
  carrier := {x | x ^ 2 ^ j = 1}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [mul_pow, hx, hy, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [inv_pow, hx, inv_one]

@[simp] lemma mem_omega {j : ℕ} {x : A} : x ∈ omega (A := A) j ↔ x ^ 2 ^ j = 1 :=
  Iff.rfl

lemma omega_mono {i j : ℕ} (hij : i ≤ j) : omega (A := A) i ≤ omega (A := A) j := by
  intro x hx
  rw [mem_omega] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add, pow_mul, hx, one_pow]

/-- The homomorphism `Ω_{k+1} → Ω_1`, `x ↦ x ^ (2 ^ k)`. -/
noncomputable def omegaHom (k : ℕ) : omega (A := A) (k + 1) →* omega (A := A) 1 where
  toFun x := ⟨x.1 ^ 2 ^ k, by
    rw [mem_omega, pow_one, ← pow_mul,
      show 2 ^ k * 2 = 2 ^ (k + 1) from (pow_succ 2 k).symm]
    exact x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := by intro x y; exact Subtype.ext (mul_pow x.1 y.1 (2 ^ k))

/-- The kernel of `x ↦ x ^ (2 ^ k) : Ω_{k+1} → Ω_1` is `Ω_k`. -/
lemma ker_omegaHom (k : ℕ) :
    (omegaHom (A := A) k).ker
      = Subgroup.comap (Subgroup.subtype (omega (A := A) (k + 1))) (omega (A := A) k) := by
  ext z
  simp only [MonoidHom.mem_ker, Subgroup.mem_comap, mem_omega, Subgroup.coe_subtype]
  constructor
  · intro hz
    have := congrArg Subtype.val hz
    simpa [omegaHom] using this
  · intro hz
    apply Subtype.ext
    simpa [omegaHom] using hz

end Basic

section Finite

variable {A : Type*} [CommGroup A] [Finite A]

omit [Finite A] in
/-- For `H ≤ K` the cardinality of `H.comap K.subtype` is that of `H`. -/
lemma card_comap_subtype_of_le {H K : Subgroup A} (h : H ≤ K) :
    Nat.card (Subgroup.comap K.subtype H) = Nat.card H := by
  have h1 : Nat.card ↥(Subgroup.map K.subtype (Subgroup.comap K.subtype H))
      = Nat.card ↥(Subgroup.comap K.subtype H) :=
    Subgroup.card_map_of_injective (K := Subgroup.comap K.subtype H) (f := K.subtype)
      K.subtype_injective
  have hKH : K ⊓ H = H := le_antisymm inf_le_right (le_inf h le_rfl)
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype, hKH] at h1
  exact h1.symm

/-- The key step: `|Ω_{k+1}| ≤ |Ω_k| * |Ω_1|`. -/
lemma card_omega_succ_le (k : ℕ) :
    Nat.card (omega (A := A) (k + 1))
      ≤ Nat.card (omega (A := A) k) * Nat.card (omega (A := A) 1) := by
  have hker : Nat.card ↥(omegaHom (A := A) k).ker = Nat.card (omega (A := A) k) := by
    rw [ker_omegaHom]
    exact card_comap_subtype_of_le (omega_mono (Nat.le_succ k))
  have hrange : Nat.card ↥(omegaHom (A := A) k).range ≤ Nat.card (omega (A := A) 1) :=
    Nat.card_le_card_of_injective (fun x : (omegaHom (A := A) k).range => (x : omega (A := A) 1))
      Subtype.coe_injective
  have h1 : Nat.card (omega (A := A) (k + 1))
      = Nat.card ↥(omegaHom (A := A) k).ker * Nat.card ↥(omegaHom (A := A) k).range := by
    rw [← (omegaHom (A := A) k).ker.card_mul_index, Subgroup.index_ker]
  rw [h1, hker]
  exact Nat.mul_le_mul_left _ hrange

omit [Finite A] in
lemma card_omega_zero : Nat.card (omega (A := A) 0) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨1, by simp⟩⟩
  apply Subtype.ext
  have hx : x.1 ^ 2 ^ 0 = 1 := x.2
  have hy : y.1 ^ 2 ^ 0 = 1 := y.2
  simp only [pow_zero, pow_one] at hx hy
  rw [hx, hy]

omit [Finite A] in
lemma card_omega_e {e : ℕ} (hexp : ∀ a : A, a ^ 2 ^ e = 1) :
    Nat.card (omega (A := A) e) = Nat.card A := by
  exact Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun x : A => x ^ 2 ^ e = 1) hexp)

end Finite

theorem card_T_eq_pow {A : Type} [CommGroup A] [Finite A] {e : ℕ}
    (hexp : ∀ a : A, a ^ 2 ^ e = 1)
    (hcard : Nat.card A = (Nat.card {x : A | x ^ 2 = 1}) ^ e) :
    ∀ j ≤ e, Nat.card {x : A | x ^ 2 ^ j = 1} = (Nat.card {x : A | x ^ 2 = 1}) ^ j := by
  set n : ℕ := Nat.card {x : A | x ^ 2 = 1} with hn
  have hne : Nonempty {x : A | x ^ 2 = 1} := ⟨⟨1, by simp⟩⟩
  have hnpos : 0 < n := by rw [hn]; exact Nat.card_pos
  -- |Ω_{k+1}| ≤ |Ω_k| * n
  have hstep : ∀ k, Nat.card (omega (A := A) (k + 1)) ≤ Nat.card (omega (A := A) k) * n :=
    fun k => card_omega_succ_le k
  -- Upper bound |Ω_j| ≤ n ^ j
  have hub : ∀ j, Nat.card (omega (A := A) j) ≤ n ^ j := by
    intro j
    induction j with
    | zero => rw [card_omega_zero, pow_zero]
    | succ j ih =>
      calc Nat.card (omega (A := A) (j + 1)) ≤ Nat.card (omega (A := A) j) * n := hstep j
        _ ≤ n ^ j * n := Nat.mul_le_mul_right _ ih
        _ = n ^ (j + 1) := by rw [pow_succ]
  -- Chain bound |Ω_{i+d}| ≤ |Ω_i| * n ^ d
  have hchain : ∀ i d, Nat.card (omega (A := A) (i + d)) ≤ Nat.card (omega (A := A) i) * n ^ d := by
    intro i d
    induction d with
    | zero => simp
    | succ d ih =>
      calc Nat.card (omega (A := A) (i + (d + 1))) = Nat.card (omega (A := A) ((i + d) + 1)) := rfl
        _ ≤ Nat.card (omega (A := A) (i + d)) * n := hstep (i + d)
        _ ≤ (Nat.card (omega (A := A) i) * n ^ d) * n := Nat.mul_le_mul_right _ ih
        _ = Nat.card (omega (A := A) i) * n ^ (d + 1) := by rw [pow_succ]; ring
  intro j hj
  have hje : j + (e - j) = e := Nat.add_sub_of_le hj
  have h1 : Nat.card (omega (A := A) e) ≤ Nat.card (omega (A := A) j) * n ^ (e - j) := by
    have hc := hchain j (e - j)
    rwa [hje] at hc
  have h1' : n ^ e ≤ Nat.card (omega (A := A) j) * n ^ (e - j) := by
    rw [card_omega_e hexp, hcard] at h1
    exact h1
  have hlow : n ^ j ≤ Nat.card (omega (A := A) j) := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hnpos (e - j))
    calc n ^ j * n ^ (e - j) = n ^ e := by rw [← pow_add, hje]
      _ ≤ Nat.card (omega (A := A) j) * n ^ (e - j) := h1'
  show Nat.card (omega (A := A) j) = n ^ j
  exact le_antisymm (hub j) hlow

end Work.Higman
